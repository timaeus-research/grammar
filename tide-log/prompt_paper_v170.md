# Consult #170 — reorganising the paper "Expectations and the Exceptional Divisor" around the polar-distribution results

You are Astra. The formalisation programme of consults #167–#169 is now in hand (grammar main `1a04563`,
915 modules, zero sorry/axiom): units 1–14 (the population polar data of the chart zeta function, route B
(B1)/(B4) for the empirical coefficients, the `x²y²` regression) and units 18–21 (the global leading measure,
the extremal certificate, the identification with the stratum measure, deep-fibre nullity). The paper draft
(grammar2, 51 pp, reproduced in full below) predates these results: it was written around the depth-graded
stratum formulas, the `IsTest`/admissibility restrictions, and the analytic derivations of the coefficients.
Consult #167 fixed the target hierarchy (§0 below) and proposed the new architecture (§3 below). Your task now
is to turn that into a CONCRETE, EXECUTABLE reorganisation that I will carry out section by section.

Please deliver, in this order:

## A. The migration map
For each section of the new architecture (§3 below: six sections + appendices), list
(a) the existing subsections (cite their current `\label`s and titles) that move there, in order, and whether
    they move verbatim, are condensed, or are rewritten;
(b) the NEW material to be written there (statements only, no proofs yet), naming the Lean declaration(s)
    that back each statement (names in the formal-state summary and the attached files);
(c) what is deleted (with the reason: superseded, wrong, or moved to an appendix).
Be explicit about the fate of every current subsection; nothing should be silently dropped.

## B. The statements to print
Give TeX-ready (theorem environments of the paper's preamble: thm/prop/lem/cor/defn, with `\label`s and the
paper's macros) statements, in the paper's notation, of:
1. the meromorphic distribution `T(s)` downstairs and its resolved presentation `T̃(s)`, the candidate order
   `M_μ`, the Laurent data `A_{μ,r}` with the `(μ−s)^{−r}` convention, and the chart formula for `A_{μ,r}` (the
   polar coefficient theorem, `chartZetaAtDepth_sub_polarPart_isBigO_one` + `chartPolarCoeff`), with support
   in the resonant locus and transverse order (`chartPolarCoeff_eq_zero_of_jetsZeroOn`, `chartPolarCoeff_congr`);
2. the transform proposition (B1, `mellin_empIntegral_eq_coupledChartZeta`) and the coupling-average formula
   (B4, `ofReal_empCoeff_eq_couplingPolarCoeff`) — as printed in #168 §2 but checked against the attached Lean
   statements (in particular the normalisation `empCoeff = (−1)^{q+1}/q! · couplingPolarCoeff`, the range
   `0 < μ < L` on the lattice, `q ≤ d−1`, the flat/bounded hypotheses);
3. the structural theorem (*) — decide how to print it honestly: B4 is formal, (*) needs the log-weighted jet
   interchange (B15–B16, not formalised). Propose the exact wording: theorem with a derivation from B4 marked
   "derivation", or corollary under an explicit interchange hypothesis;
4. the global leading measure: `ρ^λ_m` (`leadingResidueMeasureU`), the tilted `ν̂(ξ)`
   (`empiricalLeadingMeasureU`), the empirical leading theorem for every observable
   (`hasLeadingTerm_empZ_eq_integral_leadingU`), the population version, finiteness, the deep-fibre nullity
   (`leadingResidueMeasureU_deepZeroFibre`), the extremal certificate (`ExtremalCertificate`,
   `chartLeading_of_extremalData`), the identification `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on all of `U`
   (`globalExtremalStratumMeasure_eq`) and the coefficient functional for every smooth observable
   (`coeff_withF_eq_integral_globalExtremalStratumMeasure`, `tendsto_normalised_partitionObs_extremal_all`).
   Say precisely how the certificate should be presented (a hypothesis on the transport, with the sufficient
   condition "box origins in the zero fibre", `extremalCertificate_of_divPt_zero`), and how the normalisation
   convention between `ρ` (raw) and `ν` (population) is to be fixed in the text once and for all;
5. the `x²y²` example through the constant log term (`empCoeff_xy_sq_one`, `empCoeff_xy_sq_zero`,
   `tendsto_logExample`), in the form the new §1 should display.

## C. Claims in the current draft that must change
List every statement of the current draft that is now (i) proven and can drop its "derivation"/analytic
status, (ii) superseded by a stronger formal statement (e.g. `IsTest`/admissibility restrictions on the
leading term that the global measure removes), (iii) wrong or misleading in the light of the formal results
(sign conventions, normalisation `(m−1)!/Γ(λ)`, "the extended leading measure gives `D_{m+1}` measure
zero" — now a theorem, but check the surrounding claims), (iv) still unproved and must stay marked.

## D. The coverage table
Rows to add/modify in the table of §13 ("What is a theorem"), at commit `1a04563`, with hypotheses and Lean
names, for units 1–14 and 18–21; rows to delete.

## E. Order of execution and risks
Which sections to rewrite first (the dependencies of the notation), what to keep from the old text as
appendix material, and the three or four places where the reorganisation is most likely to introduce an
error (e.g. the two `s`-conventions, the Γ factor, the raw/population normalisation, the sign `(−1)^r`).

Be concrete and complete; I will execute your map directly. Where the attached Lean statements and the
draft disagree, the Lean statements win.

---
# §0/§1b/§3 of the plan (tide-log/plan_polar_distribution.md)
## 0. The target hierarchy

1. **The intrinsic object downstairs.** `⟨T(s), f⟩ = ∫_W f K^{-s} φ dw`, holomorphic for `Re s < λ`,
   with a distribution-valued meromorphic continuation. Its resolved presentation is
   `T̃(s) = (K∘π)^{-s} π^*(φ dw)` with `π_* T̃ = T`. Near a positive candidate `μ`:
   `T̃(s) = Σ_{r=1}^{M_μ} A_{μ,r}/(μ−s)^r + H_μ(s)`, the `A_{μ,r}` distributions of finite transverse
   order supported on the `μ`-resonant locus.
2. **The universal radial kernel.** Mellin in `N` of the frozen partition function is
   `⟨T̃(s), F S_s(ψ)⟩` (population: `Γ(s)⟨T̃(s),F⟩`). The empirical theory is the population
   meromorphic distribution applied to the holomorphic amplitude `F S_s(ψ)`.
3. **The all-log coefficient formula (*).** For every `μ` on the lattice and `q ≤ M_μ − 1`,
   ```
   c_{μ,q}(F;ψ) = (1/q!) Σ_{r=q+1}^{M_μ} ((−1)^{r−q−1}/(r−q−1)!) ⟨ A_{μ,r}, F ∂_s^{r−q−1} S_s(ψ)|_{s=μ} ⟩,
   ```
   population case with `Γ^{(r−q−1)}(μ)` in place of the index derivative. Top log `q = M_μ−1`:
   `c = ⟨A_{μ,M_μ}, F S_μ(ψ)⟩/(M_μ−1)!` (the graded formula); the tie case `M_μ=2` gives the paper's
   `x²y²` constants.
4. **The global leading measure.** At the first pole `(λ, m)`, `A_{λ,m}` is a finite positive measure
   `ρ_λ` (extends integrably across intersections with nonminimal walls, since those have exponent
   `> λ`); for every smooth `F`, `N^λ (log N)^{−(m−1)} Z_N[F;ψ] → (1/(m−1)!) ∫ F S_λ(ψ) dρ_λ`. No
   admissibility.
5. **Normalisation.** `Z_N^ψ ~ N^{−λ} Σ_j B_j^ψ(log N) x^j` with distribution-valued polynomial blocks;
   the posterior is its formal normalisation; leading probability measure
   `Π_ψ = p_*(S_λ(ψ)ρ_λ / ∫S_λ(ψ)dρ_λ)`. Frozen / diagonal / Gaussian limits stated separately.
6. **The branch space.** Work on the real oriented blow-up of the resolution along the divisor (sides
   separated), so that "measurable field with orthantwise smooth representatives" becomes one smooth
   field on a manifold with corners, and the leading measure lives on a compact space.

## 1b. Conventions fixed by consult #167 (gpt6_bigpicture_v167.md)

* Polar functionals EXCLUDE the radial Gamma factor: `T_{h,k}(s)[G] = ∫_{(0,1]^d} G u^{h−2ks} du`,
  `T = Σ_{r=1}^{M_μ} A_{μ,r}/(μ−s)^r + H_μ(s)`; `M_μ = #{i : 2k_iμ − h_i − 1 ∈ ℕ}` is a candidate order
  bound, not the pole order of a given pairing.
* Library convention: `polarCoeff c μ q = (−1)^{q+1} q! c_{μ,q}` and
  `polarPart D a μ s = Σ_q a q/(s−μ)^{q+1}` (PrincipalPartUniqueness.lean); eq:laurent is right.
* `A_{μ,c}[F] = ∫ F d(residueMeasure)` holds ONLY on `stratumOpen c` for tests vanishing near
  `deepZeroFibre c` under `ZeroOrder`; no sign (A uses `(μ−s)^{−r}`); the standard-Laurent
  distribution is `(−1)^c A_{μ,c}`.
* `A_{μ,1}` at one resonant coordinate `i₀` of order `α`: `(1/(2k_{i₀}α!)) FP∫ ∂^α_{i₀}G(0,w) w^{h−2kμ}dw`
  with FP the coordinatewise Taylor-subtracted finite part (16); valid for ALL α, no gap hypothesis.
* Regression: `h=0, k=(1,1), μ=1/2`: `A_{1/2,2}[G] = G(0,0)/4`,
  `A_{1/2,1}[G] = ½∫(G(x,0)−G(0,0))/x + ½∫(G(0,y)−G(0,0))/y`; `c_{1/2,1} = A_2[G S]`,
  `c_{1/2,0} = A_1[G S] − A_2[G ∂_s S]` (must match `tendsto_logExample`).
* Orthant adapters: on a signed chart with signed-root field ξ the positive-box representative is
  `ζ_σ(v) = (∏σ_i^{k_i}) ξ(σv)`; test `K=x²` (branches a,−a), `K=x⁴` (both a), `K=x²y²` (σ_xσ_y a).
* The empirical leading limit for ALL smooth F already exists (`hasLeadingTerm_empZ`); what is missing
  at the extremal pair is the MEASURE IDENTIFICATION (no leading mass on `deepZeroFibre m`), not the
  limit. `IsExtremalData` (intrinsic, support-truncated) does not imply `ChartLeading Y` for an
  arbitrary transport: an adapted local cover certificate is needed.
* Branch space: first a finite disjoint union of closed leading-face parameter boxes (compact metric,
  atlas-dependent); the intrinsic real oriented blow-up later.

F7. **Variance-2 lemma (M7)** on the greybook bridge side.

Order: F1 → F2 → F3 (the mathematical centre; chart level, ~6–10 units) → F5 (independent; ~3 units)
→ F4 (~4 units) → F7; F6 deferred.

## 3. Paper reorganisation (after F1–F3 and M4 are in hand)

New architecture (per the perspective review):
1. What a posterior expectation sees — thesis, main theorem (accessible form), one complete `x²y²`
   calculation through the constant log term, what is classical / newly formalised / new.
2. Meromorphic distributions and normal-crossing computation — `T(s)`, `T̃(s)`, actual vs candidate
   poles, support and transverse order, why crossing jets alone do not suffice, tests upstairs vs
   observables `f∘π`. (Absorbs §§2–5.)
3. Polar coefficients, residues and finite parts — all coefficients as Laurent data; the leading
   positive measure (global); associated-graded formulas; finite-part evaluation; observable
   vanishing and cancellation, with admissibility introduced before the restricted statements.
4. Universal radial tilting — `S_μ`, ladder, index derivatives, (*), the uniform expansion theorem,
   generating identity, two worked empirical calculations. (Weber/Weyl to an appendix.)
5. Posterior normalisation and the sample limit — distribution-valued blocks, formal normalisation,
   frozen / diagonal / Gaussian stated separately, source cumulants as a corollary.
6. What averaging does and does not preserve — bounded posterior convergence, critical failure of
   evidence uniform integrability (variance-2 lemma), two-site illustration, Gaussian Gibbs model in
   brief. Stein/replica/inverse-evidence/quenched-source to an appendix.
Appendices: chart proofs; finite-part computations; expansion algebra; special functions; Gaussian
Gibbs identities; formalisation coverage (a coverage document, not a source of hidden hypotheses).

---
# Consult #168 §2 'What to print in the paper' (for reference)
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


---
# Formal-state summary: HEADLINES rows DLXIII–DLXXXI (units 1–21)
| **DLXIII** | ★★ **THE POLAR AMPLITUDE ALGEBRA (u898; polar-distribution programme unit 1; Astra #167, `tide-log/plan_polar_distribution.md`)**: the sign, factorial and finite-sum bookkeeping of formula (*) of the plan, isolated before any analysis. For a polar array `a j ℓ` (read as `A_{j+1}[∂_s^ℓ g(μ)]`, with `A_r` the polar functionals of a meromorphic pairing `T(s) = Σ_r A_r/(μ−s)^r + H(s)` and `g` a holomorphic amplitude family): `polarAmplitudeCoeff D a q = Σ_{j∈[q,D]} (−1)^{j+1} a j (j−q)/(j−q)!` is the array in the library's `polarPart` convention and `logAmplitudeCoeff D a q = (1/q!) Σ_{j∈[q,D]} (−1)^{j−q} a j (j−q)/(j−q)!` the asymptotic coefficient; `polarAmplitudeCoeff_eq`: the first is `(−1)^{q+1} q!` times the second, so for real data `polarAmplitudeCoeff = polarCoeff (logAmplitudeCoeffReal)` (★ `polarAmplitudeCoeff_ofReal`). ★★ `polarAmplitudeSum_sub_polarPart`: for `s ≠ μ`, `Σ_{j≤D} P_j(s)/(μ−s)^{j+1} − polarPart D (polarAmplitudeCoeff D a) μ s = Σ_j Σ_{ℓ>j} (−1)^{j+1} a j ℓ (s−μ)^{ℓ−j−1}/ℓ!` with `P_j(s) = Σ_{ℓ≤D} a j ℓ (s−μ)^ℓ/ℓ!` — the right side is a polynomial, so the polar part of a Taylor-expanded amplitude family is exactly the array (this is what will identify `empCoeff` with `(1/q!)Σ_j ((−1)^{j−q}/(j−q)!) A_{μ,j+1}[G ∂_s^{j−q}S(·,ζ)|_μ]` once the chart zeta functionals exist). Also the top entry `polarAmplitudeCoeff D a D = (−1)^{D+1} a D 0`, vanishing above `D` and zero padding. Non-claims: no analysis — the polar functionals, the chart zeta function and its continuation are units 3–8 of the plan. | PolarAmplitudeAlgebra.lean |
| **DLXIV** | ★★ **THE CLOSED-FACE LEADING MEASURE (u899; polar-distribution programme unit 18; Astra #167 A4)**: on the box `(0,b]^d` with `J = resSet h k l` the resonant coordinates and a nonnegative continuous amplitude `a`, `leadingFaceMeasure h k l b a` is the pushforward under the face inclusion `w ↦ glue J 0 w` of the density `(∏_{i∈J}(2k_i)⁻¹) a(0_J,w) residueWeight(w)` on the complementary box `(0,b]^{Jᶜ}`. Under `l ≤ ratioExp h k i` for every `i` the complementary weight has exponents `> −1` (`integrableOn_residueWeight_compl`, from the general `integrableOn_residueWeight_box`) and the measure is FINITE (★ `leadingFaceMeasure_univ_lt_top`, `isFiniteMeasure_leadingFaceMeasure`); it is carried by the closed face `{u_J = 0}` (`leadingFaceMeasure_face`) and gives the deeper corners `{∃ i ∉ J, u_i = 0}` measure ZERO (`leadingFaceMeasure_deep`) — the extremal leading measure loses no mass at the nonminimal walls. Integrals against it are the face-construction box integrals (`integral_leadingFaceMeasure`), so the empirical face functional is `(1/(m−1)!) ∫ S_l(ξ) dρ^η` (★ `faceFunctional_eq_integral_leadingFaceMeasure`) and, under `BoxLeading h k l m` with the multiplicity attained, for EVERY continuous observable `F`, field `ξ` and nonnegative amplitude `a`: `N^l (log N)^{−(m−1)} ∫ a F u^h e^{−N u^{2k} + √N u^k ξ} → (1/(m−1)!) ∫ F S_l(ξ) dρ^a` (★★ `tendsto_empBoxIntegral_leadingFaceMeasure`; the limit is `tendsto_empBoxIntegral_div_boxFaceLimit`, the measure representation on the closed face is new). Non-claims: the resolved assembly (units 19–21: `ChartLeading` transports, then intrinsic `IsExtremalData` via an adapted local cover), the identification with `extremalStratumMeasure` extended by zero across `deepZeroFibre`. | LeadingFaceMeasure.lean |
| **DLXV** | ★★ **THE CHART ZETA FUNCTIONAL ON ITS STRIP (u900; polar-distribution programme unit 2; Astra #167 A1)**: `chartZeta G h k s = ∫_{(0,1]^ι} G(u) ∏ uᵢ^{hᵢ−2kᵢs} du` for an arbitrary finite index type, the complex weight written as `cpowWeight h k s u = exp((logSum h u) − 2 s (logSum k u))` (equal to the product of complex powers on the box, `cpowWeight_eq_prod_cpow`, with norm `∏ uᵢ^{hᵢ−2kᵢ Re s}`, `norm_cpowWeight`; its `s`-derivative is `−2 logSum k · weight`, `hasDerivAt_cpowWeight`). For a `p`-flat amplitude `|G| ≤ C ∏ uᵢ^{pᵢ}` on the box (`FlatOn`) and `s` in the flat strip `2kᵢ Re s < pᵢ + hᵢ + 1` (`FlatStrip`, open, monotone in `Re s`) the integrand is integrable (`integrableOn_chartZeta_integrand_flat`) and the functional is holomorphic with derivative the log-weighted integral `∫ G · weight · (−2 logSum k)` (★★ `hasDerivAt_chartZeta_flat`, `differentiableOn_chartZeta_flat`; dominated differentiation on a ball inside the strip with the majorant `C ∏ u^{p+h−2k(Re s+ε)} (1 + |Σ 2kᵢ log uᵢ|)` from `integrableOn_prod_rpow_mul_log_pow`); the bounded case is `p = 0` (`ZetaStrip`, `hasDerivAt_chartZeta`, `differentiableOn_chartZeta`). At a real point the functional is the face integral of the smooth engine, `chartZeta G h k μ = faceCoeffInt G h (2k) 1 μ 0` (`chartZeta_ofReal`). The flat version is what the complementary face integrals of the Taylor-subtracted amplitudes of unit 3 need on the enlarged strip `Re s < (pᵢ+hᵢ+1)/2kᵢ`. Non-claims: the continuation past the strip (units 3–5). | ChartZetaStrip.lean |
| **DLXVI** | ★★ **THE ZETA FACE-TERM IDENTITY AND THE SUBSET FORMULA ON THE STRIP (u901; polar-distribution programme unit 3; Astra #167 A1 expression (3))**: the Laplace-side face construction is mirrored on the zeta side. The inner monomial zeta integral is explicit, `∫_{(0,1]^ι} ∏ uᵢ^{eᵢ−2kᵢs} du = ∏ᵢ 1/(eᵢ+1−2kᵢs)` on the strip (`integral_box_cpowWeight`, via `Measure.restrict_pi_pi`, `integral_fintype_prod_eq_prod` and `integral_cpow`), a natural monomial is absorbed into the weight (`mono_mul_cpowWeight`), and the weight and the logarithmic sums split along a face (`cpowWeight_glue`, `logSum_glue`; complex-valued box split `integral_box_split_complex`). ★ `zeta_faceTerm_integral`: for `s` in the strip, `∫ (faceOp p J F) · weight = Σ_{m∈idxL p (lJ J)} (∏_{i∈J} 1/mᵢ!) (∏_{i∈J} 1/(mᵢ+hᵢ+1−2kᵢs)) · chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s`; ★★ `chartZeta_eq_sum_faces`: `chartZeta F h k s = Σ_{(J,m)∈faceIndex p} faceW J m · ∏_{i∈J} (mᵢ+hᵢ+1−2kᵢs)⁻¹ · chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s` — the subset formula, whose right side is the meromorphic continuation of unit 4 (each complementary functional is holomorphic on the flat strip `2kᵢ Re s < pᵢ+hᵢ+1` by the flat bound `faceAmp_bound` and DLXV). Non-claims: the continuation itself, the polar functionals (units 4–5). | ChartZetaFace.lean |
| **DLXVII** | ★★ **THE MEROMORPHIC CONTINUATION OF THE CHART ZETA FUNCTIONAL (u902; polar-distribution programme unit 4; Astra #167 A1)**: the face sum `chartZetaAtDepth p F h k s = Σ_{(J,m)∈faceIndex p} faceW J m · innerFactor h k J m s · chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s`, `innerFactor = ∏_{i∈J} 1/(mᵢ+hᵢ+1−2kᵢs)`, is defined for every `s`, equals `chartZeta F h k` on the strip (`chartZetaAtDepth_eq_chartZeta`, from DLXVI), and for positive depths is HOLOMORPHIC on the flat strip `2kᵢ Re s < pᵢ+hᵢ+1` away from the finitely many candidate poles `(mᵢ+hᵢ+1)/2kᵢ` (`PoleAt`, `finite_poleSet`, `pos_re_of_poleAt`; ★ `differentiableOn_chartZetaAtDepth`, via the flat bound `faceAmp_bound` → `flatOn_faceAmp` and the flat-strip holomorphy of DLXV). ★★ `chartZetaAtDepth_eq_of_depths`: two positive depths agree on the common flat strip off either pole set (for `Re s > −1`) — the identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the open strip `−1 < Re s < min flatEdge` minus the poles, whose preconnectedness (★ `isPreconnected_strip_diff_finite`: any strip `c₁ < Re s < c₂` minus a finite set) is transported from the plane minus a countable set (`Set.Countable.isPathConnected_compl_of_one_lt_rank`) through the `arctan` homeomorphism `stripMap` (continuous, injective, onto the strip). So `chartZeta F h k` continues meromorphically to `Re s < min_i (pᵢ+hᵢ+1)/2kᵢ`, i.e. as far as one likes with growing depth, with poles only at the candidate exponents. Non-claims: the Laurent coefficients (unit 5), the pole order bound as a statement about the assembled function. | ChartZetaRegularization.lean |
| **DLXVIII** | ★★ **THE POLAR FUNCTIONALS OF THE CHART ZETA FUNCTIONAL (u903; polar-distribution programme unit 5; Astra #167 A1)**: at a real point `μ` each face `(J,m)` of the depth-`p` face sum has the resonant coordinates `faceResSet = {i∈J : mᵢ+hᵢ+1 = 2kᵢμ}`, pole order `poleOrder = #faceResSet ≤ d`, and the exact factorisation ★ `innerFactor_eq_res`: `innerFactor h k J m s = (∏_res (2kᵢ)⁻¹) · (μ−s)^{−c} · regularFactor s` for EVERY `s`, with `regularFactor` the non-resonant product; `faceHolo = regularFactor · chartZeta (faceAmp)` is holomorphic on the open set `faceRegSet` (flat strip minus the non-resonant zeros), a neighbourhood of `μ` once `μ` lies in the flat strip. Taylor remainder for holomorphic functions (`taylor_remainder_isBigO`: `f − Σ_{k<n} f^{(k)}(c)/k! (s−c)^k = O(‖s−c‖^n)`, from Mathlib's `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` and `HasFPowerSeriesOnBall.factorial_smul`) and its polar form (`pole_taylor_isBigO_one`: `(c−s)^{−n} f(s) − Σ_{q<n} (−1)^n f^{(n−1−q)}(c)/(n−1−q)! (s−c)^{−(q+1)} = O(1)` on `𝓝[≠] c`). ★ `chartPolarCoeff p F h k μ q` (the coefficient of `(s−μ)^{−(q+1)}`): over the faces with `c ≥ q+1`, `faceW · resConst · (−1)^c · faceHolo^{(c−1−q)}(μ)/(c−1−q)!`; vanishes beyond the maximal pole order and identically when `μ` is not a candidate pole (`poleAt_iff_poleOrder`). ★★ `chartZetaAtDepth_sub_polarPart_isBigO_one`: for `F` smooth, positive depth with `μ` in the flat strip, and `D+1 ≥` every pole order, `chartZetaAtDepth p F h k − polarPart D (chartPolarCoeff p F h k μ) μ = O(1)` on `𝓝[≠] μ` — exactly the input form of `polarCoeff_unique` (DXLIII); the universal version with `D = d` (`…'`), boundedness off the poles, and the canonical-depth form ★ `chartZetaAtDepth_depthOf_sub_polarPart_isBigO_one` (`depthOf h k L`, `L ≥ L₀ h`, any real `μ < L`; `flatStrip_depthOf`). Non-claims: identification of `chartPolarCoeff` with the paper's `A_{μ,r}` in terms of face integrals of finite parts (unit 6), reality of the coefficients, and the empirical all-log formula (units 11–12). | ChartZetaPolar.lean |
| **DLXIX** | ★★ **REALITY, SUPPORT AND JET DEPENDENCE OF THE CHART POLAR COEFFICIENTS (u904; polar-distribution programme unit 6; Astra #167 A1)**: functions commuting with conjugation (`ConjSymm`) are closed under `deriv` (Mathlib `deriv_conj_conj`) and `iteratedDeriv`, and their iterated derivatives at real points are real (`ConjSymm.iteratedDeriv_ofReal`); `chartZeta G h k (conj s) = conj (chartZeta G h k s)` (`integral_conj`, `Complex.exp_conj`), the regular factors and `faceHolo` are `ConjSymm`, hence ★ every polar coefficient at a real point is REAL: `chartPolarReal p F h k μ q := (chartPolarCoeff …).re` with `ofReal_chartPolarReal`. Resonant coordinates `resCoord p h k μ = {i : ∃ m < pᵢ, m+hᵢ+1 = 2kᵢμ}` (⊇ every `faceResSet` of an admissible face), the `r`-th resonant stratum `resStratum p h k μ r = {v ∈ closedBox : #{i ∈ resCoord : vᵢ = 0} ≥ r}` (antitone in `r`; `closedFaceBox_subset_resStratum` for faces of pole order `≥ r`). ★ SUPPORT `chartPolarCoeff_eq_zero_of_jetsZeroOn`: all jets of `F` vanishing on `resStratum p h k μ (q+1)` ⇒ `chartPolarCoeff p F h k μ q = 0` (via `faceAmp_eq_zero_of_jets_zero` and `chartZeta_eq_zero_of_forall`); neighbourhood form `chartPolarCoeff_eq_zero_of_eqOn_zero` (`F = 0` on an open set containing the stratum). ★ JET CONGRUENCE `chartPolarCoeff_congr`: equal rectangular `p`-jets (`EqJetsOn`) on `resStratum p h k μ (q+1)` ⇒ equal `q`-th coefficients (face-local `faceAmp_congr_closedFaceBox`, mirroring `faceAmp_congr` on one closed face box); neighbourhood form `chartPolarCoeff_congr_of_eqOn`. Paper content: `A_{μ,q+1}` is a real distribution supported on the codimension-`(q+1)` resonant stratum and of finite order (the rectangular `p`-jet) along it. Non-claims: linearity/continuity of `F ↦ chartPolarCoeff` (unit 24), the exact-stratum ideal-power statement for lower orders (false), identification with the paper's `A_{μ,r}` face-integral formulas (unit 13). | ChartZetaPolarSupport.lean |
| **DLXX** | ★ **THE POLAR PART OF A FINITE FACE SUM (u905; route B unit B7; Astra #168)**: for an arbitrary finite family with weights `w x`, pole orders `c x ≤ D+1` and functions `f x` holomorphic near `μ`, `finiteFacePolarCoeff X w c f μ q = Σ_{x : c x ≥ q+1} w x (−1)^{c x} f x^{(c x−1−q)}(μ)/(c x−1−q)!` and ★ `finiteFaceSum_sub_polarPart_isBigO_one`: `Σ_x w x (μ−s)^{−c x} f x s − polarPart D (finiteFacePolarCoeff …) μ = O(1)` on `𝓝[≠] μ` (from `pole_taylor_isBigO_one`); unit 5's `chartPolarCoeff` is the instance `w = faceW·resConst`, `c = poleOrder`, `f = faceHolo` (`chartPolarCoeff_eq_finiteFacePolarCoeff`, `rfl`). Non-claims: nothing analytic — the lemma is the algebraic core reused by the empirical continuation (B12). | FiniteFacePolar.lean |
| **DLXXI** | ★★ **THE COUPLED CHART ZETA FUNCTIONAL (u906; route B units B8–B9; Astra #168)**: for a real coupling family `H : ℝ → (ι → ℝ) → ℝ` with the flat growth bound `|H τ w| ≤ C(1+τ)^R e^{Mτ} w^p` (`FlatOn (H τ) p (C(1+τ)^R e^{Mτ})`, the form of `growthLE_faceAmp_fieldFam`) and jointly continuous, `coupledChartZeta H h k s = ∫_0^∞ t^{s−1} e^{−t} chartZeta (H √t) h k s dt` (kernel `coupKernel s t = t^{s−1}e^{−t}`, `norm_coupKernel`, `hasDerivAt_coupKernel`), the log moments `coupledLogMoment H h k n s = ∫∫_{(0,∞)×(0,1]^ι} t^{s−1} e^{−t} H(√t,w) w^{h−2ks} (log t − 2 logSum k w)^n` on the product measure `coupMeasure ι`, the envelopes (`rpow_sub_one_le_add`: `t^{σ−1} ≤ t^{a−1} + t^{b−1}` for `a ≤ σ ≤ b`; `integrableOn_coupEnvelope_t` from `integrableOn_envelope`; the box envelope of `SmoothLogIntegrable`; `integrable_coupEnvelope` via `Integrable.mul_prod`) and the pointwise bound `norm_coupIntegrand_le` for `a ≤ Re s ≤ b`; ★ `integrable_coupIntegrand` and `coupledChartZeta_eq_logMoment_zero` (Fubini `integral_prod`) on the POSITIVE flat strip `0 < Re s ∧ FlatStrip p h k s`; ★★ `hasDerivAt_coupledLogMoment` (dominated differentiation `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the product measure with the single multiplier `log t − 2 logSum k w`), `iteratedDeriv_coupledLogMoment`, ★★ `iteratedDeriv_coupledChartZeta : iteratedDeriv n (coupledChartZeta H h k) s = coupledLogMoment H h k n s` and `differentiableOn_coupledChartZeta` on the positive flat strip; `EventuallyEq.iteratedDeriv_eq_of_nhds` (iterated derivatives of locally equal functions agree). Non-claims: the identification with `mellin (empIntegral)` (B10), the face-sum continuation (B11). | CoupledChartZeta.lean |
| **DLXXII** | ★★ **THE MELLIN TRANSFORM OF THE EMPIRICAL CHART INTEGRAL IS THE COUPLED CHART ZETA FUNCTIONAL (u907; route B unit B10, identity (B1); Astra #168)**: `mellin (empIntegral η ζ h k) s = coupledChartZeta (fieldFam η ζ) h k s = ∫_0^∞ t^{s−1} e^{−t} chartZeta (η e^{√t ζ}) h k s dt` on the initial strip `0 < Re s`, `2kᵢ Re s < hᵢ+1` (★★ `mellin_empIntegral_eq_coupledChartZeta`): the Mellin double integrand `N^{s−1} η v^h e^{−Nv^{2k}+√N v^k ζ}` is absolutely integrable on `(0,∞)×(0,1]^d` (★ `integrable_mellinEmpIntegrand`, AM–GM majorant `exp_tilt_le` → `|η| v^h e^{M²/2} N^{σ−1} e^{−N v^{2k}/2}`, inner Gamma integral `integral_rpow_mul_exp_neg_mul_rpow`, outer population zeta integrand `∏ vᵢ^{hᵢ−2kᵢσ}`); first Fubini interchange, the inner Mellin integral by the substitution `N = t/v^{2k}` (`mellin_exp_tilt`: `∫ N^{s−1} e^{−NK+√NH} = K^{−s} S(s, H/√K)`, with `√(v^{2k}) = v^k` and `v^h (v^{2k})^{−s} = cpowWeight h k s v`, `mono_mul_cpow_neg`), giving `∫_box η(v) v^{h−2ks} S(s, ζ(v)) dv`; unfolding `S` and the second interchange (the coupled envelope of DLXXI, `integrable_coupIntegrand` for the field family with `flatOn_fieldFam`: `|η e^{τζ}| ≤ C e^{Mτ}`). Side conditions of `polarCoeff_unique` for the empirical integral: ★ `locallyIntegrableOn_empIntegral` and ★ `empIntegral_isBigO_one_zero` (from `MellinTiltIntegrable` with the data cut off by the indicator of the closed box, `empIntegral_eq_integral_tilt`; `IsFiniteMeasure` of Lebesgue measure on the box). Non-claims: the continuation of the coupled face sum and its identification with `mellinContinuation` (B11), the polar coefficients (B12). | EmpiricalChartMellin.lean |
| **DLXXIII** | ★★ **THE COUPLED FACE SUM IS THE MELLIN CONTINUATION OF THE EMPIRICAL INTEGRAL (u908; route B unit B11; Astra #168)**: `coupledFaceZeta p η ζ h k J m s = ∫_0^∞ t^{s−1}e^{−t} chartZeta (faceAmp p J (η e^{√tζ}) m) h_{Jᶜ} k_{Jᶜ} s dt` and the coupled face sum `empZetaAtDepth p η ζ h k s = Σ_x faceW · innerFactor · coupledFaceZeta` (μ-independent); the face amplitudes of the field family are uniformly flat with exponential growth (`flatOn_faceAmp_fieldFam`, from `growthLE_faceAmp_fieldFam`), so ★ `differentiableOn_empZetaAtDepth` on the positive flat strip off `PoleAt`; ★ `empZetaAtDepth_eq_mellin`: `= mellin (empIntegral)` on the initial strip (DLXXII + the face decomposition `chartZeta_eq_sum_faces` at every coupling, marginal integrability `integrable_coupKernel_mul_chartZeta` from `Integrable.integral_prod_left`); ★★ `empZetaAtDepth_eq_mellinContinuation`: at the canonical depth `depthOf h k L` (`L ≥ L₀ h`), `empZetaAtDepth = mellinContinuation (Qamb k) (d−1) (empIntegral η ζ h k) (empCoeff η ζ h k) L` on `{0 < Re s < L}` off the candidate poles and the lattice points `latticeBelow (Qamb k) L` — identity theorem (`isPreconnected_strip_diff_finite`) seeded at `s = 1/(2 Qamb k)` on the substrip `0 < Re s < 1/Qamb k` below every ratio exponent (`inv_Qamb_le_ratioExp`, `zetaStrip_of_re_lt_inv_Qamb`), where the empirical coefficients vanish (`empCoeff_eq_zero_of_lt_inv_Qamb` via `BoxLeading`/`empCoeff_eq_zero_of_boxLeading_lt`) so that `mellin_eq_mellin_cutoffRemainderFun_add_principalParts` applies; holomorphy of the continuation off the lattice (`differentiableOn_mellinContinuation_emp`); ★ local form `empZetaAtDepth_eventuallyEq_mellinContinuation` on `𝓝[≠] μ` for every `0 < μ < L`. Non-claims: the polar coefficients and their identification (B12). | EmpiricalMellinContinuation.lean |
| **DLXXIV** | ★★★ **THE EMPIRICAL COEFFICIENTS ARE THE POLAR DATA OF THE COUPLED FACE SUM (u909; route B unit B12 — FIRST COMPLETION MILESTONE of the polar-distribution programme; Astra #168)**: at a real `μ` the coupled face sum factorises as `Σ_x faceW·resConst·(μ−s)^{−c_x}·empFaceHolo_x` with `empFaceHolo = regularFactor · coupledFaceZeta` holomorphic on the positive regular set of the face (`differentiableOn_empFaceHolo`, a neighbourhood of `μ` for `0 < μ` in the flat strip); the integrated polar coefficients `empIntegratedPolarCoeff p η ζ h k μ q = Σ_{x : c_x ≥ q+1} faceW resConst (−1)^{c_x} empFaceHolo_x^{(c_x−1−q)}(μ)/(c_x−1−q)!` (an instance of `finiteFacePolarCoeff`, DLXX) satisfy ★★ `empZetaAtDepth_sub_polarPart_isBigO_one`: `empZetaAtDepth − polarPart (d−1) (…) μ = O(1)` on `𝓝[≠] μ`, transported to the Mellin continuation by DLXXIII (`mellinContinuation_emp_sub_polarPart_isBigO_one`); hence by `polarCoeff_unique` (DXLIII) ★★★ `empIntegratedPolarCoeff_eq_polarCoeff`: for lattice points `0 < μ < L` (`L ≥ L₀ h`) and `q ≤ d−1`, `empIntegratedPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q = (−1)^{q+1} q! empCoeff η ζ h k μ q`, i.e. ★★★ `ofReal_empCoeff_eq_empIntegratedPolarCoeff`: `empCoeff η ζ h k μ q = (−1)^{q+1}/q! · empIntegratedPolarCoeff …`; canonical-cutoff form `ofReal_empCoeff_eq_empIntegratedPolarCoeff_cutoff` for `μ = m/Qamb k > 0`. Paper content: the coefficients of `N^{−μ}(log N)^q` in the empirical expansion, originally defined through the real face construction, are the Laurent coefficients at `μ` of `Σ_x faceW · innerFactor_x(s) · ∫_0^∞ t^{s−1}e^{−t} ζ_{faceAmp(η e^{√tζ})}(s) dt` — the empirical partition function's Mellin transform is the Γ-weighted coupling average of the chart zeta functionals of the tilted amplitudes. Non-claims: the coupling-average form (B4) with `chartPolarCoeff (fieldFam η ζ √t)` inside the `t`-integral (B13), reality, the amplitude form (*), `q ≥ d` (a separate support statement). | EmpiricalIntegratedPolar.lean |
| **DLXXV** | ★ **LOG MOMENTS OF THE CHART ZETA FUNCTIONAL AND THE COUPLING INTERCHANGE (u910; route B unit B13a; Astra #168)**: the box log moments `chartZetaLogMoment G h k n s = ∫_{(0,1]^ι} G w^{h−2ks} (−2 logSum k w)^n` are the derivatives of the chart zeta functional on the flat strip for flat amplitudes (`hasDerivAt_chartZetaLogMoment` by dominated differentiation with the log envelope, ★ `iteratedDeriv_chartZeta_flat`, `iteratedDeriv_chartZeta_eq_logMoment`); the binomial split of the coupled integrand (`coupTerm`, `coupIntegrand_eq_sum_coupTerm` via `add_pow`), its envelope bound and integrability (`norm_coupTerm_le`, `integrable_coupTerm`), the marginal integrability `integrable_coupKernel_logpow_mul_logMoment`, and ★ `coupledLogMoment_eq_sum`: `coupledLogMoment H h k n s = Σ_{a ≤ n} C(n,a) ∫_0^∞ t^{s−1}e^{−t}(log t)^a chartZetaLogMoment (H √t) h k (n−a) s dt`; normalised Taylor coefficients `taylorCoeff f μ n = f^{(n)}(μ)/n!` with the Cauchy-product Leibniz rule `taylorCoeff_mul` (Mathlib `iteratedDeriv_fun_mul`). Non-claims: the regrouping into (B4) (B13b). | CoupledPolarInterchange.lean |
| **DLXXVI** | ★★★ **THE EMPIRICAL ALL-LOG FORMULA IN COUPLING-AVERAGE FORM (B4) (u911; route B unit B13b; Astra #168)**: `couplingPolarCoeff p η ζ h k μ q = Σ_{j ∈ Ico q d} ((j−q)!)⁻¹ ∫_0^∞ t^{μ−1}(log t)^{j−q} e^{−t} chartPolarCoeff p (η e^{√t ζ}) h k μ j dt` and ★★★ `empIntegratedPolarCoeff_eq_couplingPolarCoeff` (for `0 < μ` in the flat strip of a positive depth), hence ★★★ `ofReal_empCoeff_eq_couplingPolarCoeff`: `empCoeff η ζ h k μ q = (−1)^{q+1}/q! · couplingPolarCoeff (depthOf h k L) η ζ h k μ q` for lattice `0 < μ < L`, `q ≤ d−1` (and `couplingPolarCoeff_eq_polarCoeff`). Proof = normalised Taylor-coefficient convolution: `taylorCoeff_coupledFaceZeta` (Taylor coefficients of the coupled face zeta = split log moments, from DLXXI + DLXXV), `taylorCoeff_chartZeta_faceAmp` (box log moments), analyticity at `μ` of `regularFactor`, `coupledFaceZeta`, `chartZeta(faceAmp)`, Leibniz `taylorCoeff_faceHolo_eq`, the marginal integrability `integrable_coupKernel_logpow_mul_taylorCoeff_faceHolo`, ★★ `taylorCoeff_empFaceHolo_eq`: `tc(R_x Φ_x)(n) = Σ_{a≤n} (a!)⁻¹ ∫ t^{μ−1}e^{−t}(log t)^a tc(R_x ζ_{x,t})(n−a) dt` (double-sum interchange over `i+a ≤ n`, `Finset.sum_comm'`), and the face/`j` regrouping (`Finset.sum_Ico_eq_sum_range`, `sum_comm'`). Paper content (Astra #168 §2): the empirical coefficient of `N^{−μ}(log N)^q` is the Γ-weighted coupling average of the population polar functionals `A_{μ,r}` of the tilted amplitudes `η e^{√tζ}`; for `ζ = 0` the inner coefficients are `t`-independent and the `t`-integrals are `Γ^{(j−q)}(μ)`. Non-claims: the amplitude form (*) with `η · ∂_s^{j−q} S(s,ζ)|_μ` (needs the log-weighted jet interchange, B15–B16), the regressions (unit 14), reality of `couplingPolarCoeff`. | EmpiricalCouplingAllLog.lean |
| **DLXXVII** | ★★ **REGRESSION OF THE COUPLING-AVERAGE FORMULA AGAINST THE x²y² EXAMPLE (u912; unit 14 — FIRST MILESTONE of Astra #167/#168)**: determination lemmas ★ `chartZetaAtDepth_eventuallyEq_of_eqOn_strip` (the meromorphic face sum is determined by the strip values of `chartZeta`: any `g` holomorphic on `−1 < Re s < flatEdge` minus a finite set agreeing with `chartZeta F h k` on the initial strip agrees with `chartZetaAtDepth` on a punctured neighbourhood of every `μ` in the flat strip; identity theorem) and ★ `chartPolarCoeff_eq_of_eventuallyEq` (the chart polar coefficients are the principal-part coefficients of any local representative, `polarPart_eq_of_sub_isBigO_one`); the `x²y²` unit square with a constant amplitude `c`: `chartZeta c 0 (1,1) s = c/(1−2s)² = (c/4)/(s−½)²`, hence `chartPolarCoeff … ½ 1 = c/4`, `… ½ 0 = 0` (`chartPolarCoeff_const_xy_sq`); with the constant field `a` the tilted amplitudes are the constants `e^{a√t}`, so ★★ `couplingPolarCoeff_xy_sq`: `couplingPolarCoeff (2,2) 1 a 0 (1,1) ½ 1 = S_{½}(a)/4`, `… ½ 0 = ∂_ν S_ν(a)|_{½}/4`, and by (B4) ★★★ `empCoeff_xy_sq_one`: `empCoeff 1 a 0 (1,1) ½ 1 = S_{½}(a)/4`, ★★★ `empCoeff_xy_sq_zero`: `empCoeff 1 a 0 (1,1) ½ 0 = −∂_ν S_ν(a)|_{½}/4` — EXACTLY the constants of the independently proved direct asymptotic `tendsto_logExample` (`4√n ∫∫ e^{−n x²y² + a√n xy} − (log n · S_{½}(a) − ∂_ν S_ν(a)|_{½}) → 0`), restated as ★ `tendsto_logExample_empCoeff`. For `a = 0`: `√π/4` and `−Γ'(½)/4`. Non-claims: the identification `empIntegral 1 a 0 (1,1) = logExample a` as functions (the regression is at the level of coefficients), the digamma special value. | PolarTwoDimExamples.lean |
| **DLXXVIII** | ★★★ **THE LEADING MEASURES ON THE RESOLVED SPACE AND THE LEADING THEOREM FOR EVERY OBSERVABLE (u913; polar-distribution plan unit 19; Astra #169)**: unconditional integral formulas for the library's face measures on `U` (`integral_faceMeasureU`, `integral_empFaceMeasureU`: `∫ G d(faceMeasureU p J μ) = ∫ faceDensity · G∘faceMap d(faceRef)`); every smooth observable is bounded on the compact face of a piece (`exists_bound_faceMap`); at the LEADING face `J = resSet (hA p) (kA p) λ` of a `BoxLeading` piece the complementary walls carry exponents `> λ`, so the face density and its tilt are integrable against every bounded observable WITHOUT a test hypothesis (★ `integrable_faceDensity_mul_leading` via unit 18's `integrableOn_residueWeight_compl` and a uniform bound of the transport density on `Base × [0,a]^{Jᶜ}`; `integrable_empFaceDensity_mul_leading`); ★ `integral_pieceFaceLimit_eq_faceRef`: for an attaining piece `∫_{Base} pieceFaceLimit dν_p = residueConst λ m · ∫ empFaceDensity · F∘faceMap d(faceRef)` for EVERY observable. The raw leading measure `leadingResidueMeasureU λ m = Σ_p Σ_{J ∈ simpleFaces p λ m} faceMeasureU Y p J λ` and the tilted `empiricalLeadingMeasureU ξ λ m = Γ(λ)/(m−1)! · Σ_p Σ_J empFaceMeasureU Y p J ξ λ` on `U`; `eq_resSet_of_mem_simpleFaces`; integrability of smooth observables against every simple-face measure of a chart-leading piece (`integrable_empFaceMeasureU_of_bounded`, `integrable_faceMeasureU_of_bounded`), `integral_empiricalLeadingMeasureU`, `empiricalLeadingMeasureU_zero` (zero field = `residueConst • raw`), ★★★ `hasLeadingTerm_empZ_eq_integral_leadingU`: at a chart-leading pair and for a bounded root field, `Z^{emp}_N[F;ξ] ~ (∫_U F dν̂^λ_m(ξ)) N^{−λ}(log N)^{m−1}` for EVERY observable `F` (no `IsTest`), ★★ `hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU`: the population `Z_N[F] ~ residueConst λ m · (∫_U F dρ^λ_m) N^{−λ}(log N)^{m−1}`; ★ both measures are FINITE at a chart-leading pair (`isFiniteMeasure_empiricalLeadingMeasureU`, `isFiniteMeasure_leadingResidueMeasureU`). Normalisation (Astra #169): the raw measure is `(m−1)!/Γ(λ)` times the population coefficient measure. Non-claims: the deep-fibre nullity `ρ (deepZeroFibre m) = 0` (needs the intrinsic-depth/coordinate-wall bridge), the face-trace-compatible form with `S_λ(ξ.ψ)` (the tilt is through the branch traces `ξ.loc`), `IsExtremalData ⇒ ChartLeading` (unit 20), the comparison with `extremalStratumMeasure` (unit 21). | ResolvedLeadingMeasure.lean |
| **DLXXIX** | ★★★ **EXTREMAL LOCALISATION OF THE LEADING MEASURE (u914; polar-distribution plan unit 20; Astra #169)**: the bridge `hasLeadingTerm_iff_tendsto_normalised` between the library's two normalisation conventions (`Z/(N^{−λ}(log N)^k) → c` iff `N^λ(log N)^{−k}Z → c`); the wall multiset `pieceWalls p = {(k_i, h_i)}` of a piece equals the intrinsic pair data of the box origin (`pairs_divPt_zero`, via `wallsAt_facePt_eq` at `J = univ`); the **extremal certificate** `ExtremalCertificate Y : ∀ p, ∃ P ∈ zeroFibre, pieceWalls p ≤ pairs P` (holds when the box origins lie in the zero fibre, `extremalCertificate_of_divPt_zero`); a wall of ratio exactly `λ` resonates with `λ` (`resonates_of_ratioExp_eq`); ★★ `chartLeading_of_extremalData`: `IsExtremalData λ m ∧ ExtremalCertificate ⟹ ChartLeading λ m` (ratio bound from clause 1; `multCount ≤ card(filter Resonates pieceWalls) ≤ resonanceCount P ≤ m` by `Multiset.monotone_filter_right`/`filter_le_filter`/`card_le_card`); ★★★ `coeff_withF_eq_integral_leadingResidueMeasureU`: at the extremal pair and under the certificate, `𝒯^U_{λ*,m*−1}[G] = Γ(λ*)/(m*−1)! · ∫_U G dρ^{λ*}_{m*}` for EVERY smooth `G` (uniqueness of limits between `tendsto_normalised_Z_of_extremalData` and unit 19's leading theorem; no test hypothesis, no deep-fibre condition); `coeff_one_eq_mass_leadingResidueMeasureU` (the partition-function coefficient is the total mass); ★★★ `tendsto_normalised_partitionObs_extremal_all` and `partitionObs_isEquivalent_extremal_all`: downstairs, `∫ prior · f · e^{−NK} ∼ Γ(λ*)/(m*−1)! (∫_U f∘π dρ^{λ*}_{m*}) N^{−λ*}(log N)^{m*−1}` for every smooth `f` (the `h0` test hypothesis of `tendsto_normalised_partitionObs_extremal` is gone, at the price of the certificate). Non-claims: the certificate is a hypothesis (it fails exactly for pieces whose walls miss the zero fibre); the comparison with `extremalStratumMeasure` (unit 21, needs the deep-fibre nullity); the existence of an adapted transport. | ResolvedExtremalLocalisation.lean |
| **DLXXX** | ★★★ **THE GLOBAL LEADING MEASURE AND THE EXTREMAL STRATUM MEASURE (u915; polar-distribution plan unit 21; Astra #169)**: the raw leading measure restricted to the open stratum `X = U ∖ D_{m+1}` (`leadingResidueMeasureX = ρ.comap val`, `integral_leadingResidueMeasureX`, `leadingResidueMeasureX_apply`); regularity of the raw measure at a chart-leading pair (`regular_leadingResidueMeasureU`: a finite measure on the σ-compact metrisable manifold `U`; `regular_leadingResidueMeasureX` via `Regular.comap'` along the open embedding); ★★★ `extremalStratumMeasure_eq_leadingResidue`: under the extremal data and the certificate, `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X` (the uniqueness theorem `eq_stratumMeasure_of_tests` applied to the regular measure `ofReal(residueConst) • ρ|_X`, whose test integrals are the coefficient functional by unit 20); `extremalStratumMeasure_univ` (total mass `Γ(λ*)/(m*−1)! · ρ(X)`), ★ `isFiniteMeasure_extremalStratumMeasure`; the GLOBAL extremal stratum measure `globalExtremalStratumMeasure = ν.map val` on `U` with ★★★ `globalExtremalStratumMeasure_eq_restrict`: `= Γ(λ*)/(m*−1)! · ρ|_{U ∖ D_{m*+1}}`, and ★★ `globalExtremalStratumMeasure_eq_iff`: `= Γ(λ*)/(m*−1)! · ρ` on all of `U` IFF `ρ(D_{m*+1} ∩ Z₀) = 0`; `integral_globalExtremalStratumMeasure`. Normalisation (Astra #169): the stratum measure is the population coefficient measure; the raw measure is its `(m*−1)!/Γ(λ*)`-multiple. Non-claims: the deep-fibre nullity `ρ(D_{m*+1} ∩ Z₀) = 0` itself (intrinsic-depth/coordinate-wall bridge; it would collapse the iff to an equality). | SmoothGlobalLeadingMeasure.lean |
| **DLXXXI** | ★★★ **DEEP-FIBRE NULLITY AND THE GLOBAL IDENTIFICATION (polar-distribution plan unit 21, closing the deferral; Astra #169)**: the coordinate hyperplanes of the complementary walls are null for the face reference measure (`faceRef_exists_eq_zero_null`, `Measure.pi_hyperplane`); a face of `m` walls maps a box point into the deep fibre `D_{m+1} ∩ Z₀` only when a complementary chart coordinate vanishes (`exists_eq_zero_of_faceMap_mem_deepZeroFibre`, the intrinsic-depth/coordinate-wall bridge `depth_divPt_eq`); ★ `faceMeasureU_deepZeroFibre`, ★★ `leadingResidueMeasureU_deepZeroFibre`: `ρ^λ_m(D_{m+1} ∩ Z₀) = 0` for EVERY `(λ, m)` (no extremality needed), `leadingResidueMeasureU_restrict_stratumOpen`; hence ★★★ `globalExtremalStratumMeasure_eq`: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on all of `U` under the extremal data and the certificate, ★★★ `coeff_withF_eq_integral_globalExtremalStratumMeasure`: the coefficient functional at the extremal pair is the global stratum measure for EVERY smooth observable (no test hypothesis), and the total mass is `Γ(λ*)/(m*−1)! · ρ(U)` (`extremalStratumMeasure_univ`). The paper's claim that the extended leading measure gives `D_{m+1}` measure zero is now a theorem. | SmoothGlobalLeadingMeasure.lean |

---
# Attached Lean files (verbatim)

## Grammar/ChartZetaPolar.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaRegularization
import Grammar.PrincipalPartUniqueness

/-!
# Chart zeta polar functionals (unit 5)

At a real point `μ` the face sum `chartZetaAtDepth p F h k` (unit 4) is a finite sum of terms
`faceW · innerFactor · chartZeta (faceAmp)`, and each inner factor is a product of the simple
rational functions `1/(mᵢ + hᵢ + 1 − 2kᵢ s)` over `i ∈ J`.  The coordinates with
`mᵢ + hᵢ + 1 = 2kᵢ μ` are *resonant* at `μ`; they contribute the pole `(μ − s)^{−c}` of order
`c = c(J, m, μ)` (the number of resonant coordinates) times the constant `∏_res (2kᵢ)⁻¹`, and the
remaining factors together with the complementary chart zeta function form a function
`faceHolo` holomorphic near `μ`.

The polar coefficients `chartPolarCoeff p F h k μ q` (the coefficient of `(s − μ)^{−(q+1)}`) are
the Taylor coefficients of the holomorphic factors, summed over the faces whose pole order
exceeds `q`, and the main theorem `chartZetaAtDepth_sub_polarPart_isBigO_one` states that
`chartZetaAtDepth − polarPart D (chartPolarCoeff …) μ = O(1)` on a punctured neighbourhood of
`μ`, which is the form consumed by the uniqueness theorem `polarCoeff_unique` of
`PrincipalPartUniqueness`.  The Taylor remainder bound for holomorphic functions
(`taylor_remainder_isBigO`) is derived from Mathlib's power-series remainder
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow` and the identification
`HasFPowerSeriesOnBall.factorial_smul` of the coefficients with iterated derivatives.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Taylor remainders of holomorphic functions -/

section Taylor

/-- Taylor remainder bound: a function holomorphic on a neighbourhood of `c` agrees with its
degree-`< n` Taylor polynomial at `c` up to `O(‖s − c‖^n)`. -/
theorem taylor_remainder_isBigO {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k)
      =O[𝓝 c] fun s => ‖s - c‖ ^ n := by
  obtain ⟨P, r, H⟩ := hf.analyticAt hU
  have hB := H.hasFPowerSeriesAt.isBigO_sub_partialSum_pow n
  have hpart : ∀ y : ℂ, P.partialSum n y =
      ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * y ^ k := by
    intro y
    unfold FormalMultilinearSeries.partialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 := H.factorial_smul y k
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at h1
    simp only [Finset.prod_const, Finset.card_fin, smul_eq_mul, nsmul_eq_mul] at h1
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    set A := (P k) fun _ => y
    set B := iteratedDeriv k f c
    clear_value A B
    field_simp
    linear_combination h1
  have hT : Tendsto (fun s : ℂ => s - c) (𝓝 c) (𝓝 0) := by
    have := (continuous_id.sub continuous_const).tendsto c (f := fun s : ℂ => s - c)
    simpa using this
  refine (hB.comp_tendsto hT).congr' ?_ ?_
  · filter_upwards with s
    simp [Function.comp, hpart]
  · filter_upwards with s
    rfl

/-- The principal part of `(c − s)^{−n} f(s)` at `c` for `f` holomorphic near `c`: the
coefficient of `(s − c)^{−(q+1)}` is `(−1)^n f^{(n−1−q)}(c)/(n−1−q)!`, and the difference is
bounded on a punctured neighbourhood of `c`. -/
theorem pole_taylor_isBigO_one {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => (c - s)⁻¹ ^ n * f s - ∑ q ∈ range n,
      (-1) ^ n * iteratedDeriv (n - 1 - q) f c / ((n - 1 - q)! : ℂ) / (s - c) ^ (q + 1))
      =O[𝓝[≠] c] fun _ => (1 : ℂ) := by
  obtain ⟨C, hC⟩ := (taylor_remainder_isBigO hU hf n).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hsc
  have hsc' : s - c ≠ 0 := sub_ne_zero.2 hsc
  have hid : (c - s)⁻¹ ^ n * f s - ∑ q ∈ range n,
      (-1) ^ n * iteratedDeriv (n - 1 - q) f c / ((n - 1 - q)! : ℂ) / (s - c) ^ (q + 1) =
      (c - s)⁻¹ ^ n *
        (f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k) := by
    rw [mul_sub, Finset.mul_sum, ← Finset.sum_range_reflect
      (fun k => (c - s)⁻¹ ^ n * ((k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k)) n]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < n := Finset.mem_range.1 hq
    have hpow : (s - c) ^ n = (s - c) ^ (n - 1 - q) * (s - c) ^ (q + 1) := by
      rw [← pow_add]; congr 1; omega
    have hcs : c - s = -(s - c) := by ring
    rw [hcs, inv_neg, neg_pow (s - c)⁻¹, inv_pow, hpow]
    field_simp
  rw [hid, norm_mul, norm_pow, norm_inv, norm_sub_rev, norm_one, mul_one]
  calc ‖s - c‖⁻¹ ^ n * ‖f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k‖
      ≤ ‖s - c‖⁻¹ ^ n * (C * ‖‖s - c‖ ^ n‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = C := by
        have h0 : ‖s - c‖ ≠ 0 := norm_ne_zero_iff.2 hsc'
        rw [Real.norm_of_nonneg (by positivity), inv_pow, inv_mul_eq_div, mul_div_assoc,
          div_self (pow_ne_zero n h0), mul_one]

end Taylor

/-! ### Resonant coordinates and the factorisation of the inner factor -/

section Faces

variable {d : ℕ}

/-- The resonant coordinates of the face `(J, m)` at `μ`: `i ∈ J` with `mᵢ + hᵢ + 1 = 2kᵢ μ`. -/
noncomputable def faceResSet (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    Finset (Fin d) :=
  J.filter fun i => ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

theorem mem_faceResSet {h k : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ} {μ : ℝ}
    {i : Fin d} :
    i ∈ faceResSet h k J m μ ↔ i ∈ J ∧ ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ :=
  Finset.mem_filter

theorem faceResSet_subset (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    faceResSet h k J m μ ⊆ J :=
  Finset.filter_subset _ _

/-- The pole order `c(J, m, μ)` of the face `(J, m)` at `μ`. -/
noncomputable def poleOrder (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ℕ :=
  (faceResSet h k J m μ).card

theorem poleOrder_le_card (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ J.card :=
  Finset.card_le_card (faceResSet_subset h k J m μ)

theorem poleOrder_le (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ d :=
  (poleOrder_le_card h k J m μ).trans (by simpa using Finset.card_le_univ J)

/-- The resonant constant `∏_{i resonant} (2kᵢ)⁻¹`. -/
noncomputable def resConst (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ℂ :=
  ∏ i ∈ faceResSet h k J m μ, (2 * ((k i : ℕ) : ℂ))⁻¹

/-- The non-resonant part of the inner factor, holomorphic near `μ`. -/
noncomputable def regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    (μ : ℝ) (s : ℂ) : ℂ :=
  ∏ i ∈ J \ faceResSet h k J m μ, 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1)

/-- A resonant denominator is `2kᵢ (μ − s)`. -/
theorem denom_eq_of_mem_faceResSet {h k : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ}
    {μ : ℝ} {i : Fin d} (hi : i ∈ faceResSet h k J m μ) (s : ℂ) :
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 = 2 * ((k i : ℕ) : ℂ) * ((μ : ℂ) - s) := by
  have hres := (mem_faceResSet.1 hi).2
  have hC : ((m i : ℂ) + (h i : ℂ) + 1) = 2 * ((k i : ℕ) : ℂ) * (μ : ℂ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hres
    push_cast at this
    exact this
  push_cast
  linear_combination hC

/-- ★ **Factorisation of the inner factor at `μ`**:
`innerFactor = (∏_res (2kᵢ)⁻¹) · (μ − s)^{−c} · regularFactor`, valid for every `s`. -/
theorem innerFactor_eq_res (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ)
    (s : ℂ) :
    innerFactor h k J m s =
      resConst h k J m μ * ((μ : ℂ) - s)⁻¹ ^ poleOrder h k J m μ * regularFactor h k J m μ s := by
  unfold innerFactor resConst regularFactor poleOrder
  have e : (∏ i : {i // inJ J i},
      1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) =
      ∏ i ∈ J, 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1) :=
    (Finset.prod_subtype J (p := fun i => inJ J i) (fun _ => Iff.rfl)
      (fun i => 1 / (((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1))).symm
  rw [e, ← Finset.prod_sdiff (faceResSet_subset h k J m μ), mul_comm]
  congr 1
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [denom_eq_of_mem_faceResSet hi s, one_div, mul_inv]

/-- The regular factor is holomorphic wherever its denominators do not vanish. -/
theorem differentiableOn_regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    (μ : ℝ) {U : Set ℂ}
    (hU : ∀ s ∈ U, ∀ i ∈ J \ faceResSet h k J m μ,
      ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0) :
    DifferentiableOn ℂ (regularFactor h k J m μ) U := by
  unfold regularFactor
  refine differentiableOn_finset_prod' _ fun i hi => ?_
  refine (differentiableOn_const _).div ?_ fun s hs => hU s hs i hi
  exact ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).add
    (differentiableOn_const _)

/-- The set on which the face `(J, m)` is regular at depth `p`: the flat strip minus the
zeros of the non-resonant denominators. -/
def faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) : Set ℂ :=
  {s | FlatStrip p h k s ∧ ∀ i ∈ J \ faceResSet h k J m μ,
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0}

theorem isOpen_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    IsOpen (faceRegSet p h k J m μ) := by
  have : faceRegSet p h k J m μ = {s | FlatStrip p h k s} ∩
      ⋂ i ∈ J \ faceResSet h k J m μ,
        {s : ℂ | ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0} := by
    ext s; simp [faceRegSet]
  rw [this]
  refine (FlatStrip.isOpen p h k).inter (isOpen_biInter_finset fun i _ => ?_)
  exact isOpen_ne_fun (((continuous_const).sub (continuous_const.mul continuous_id)).add
    continuous_const) continuous_const

/-- `μ` itself lies in the regular set once it lies in the flat strip. -/
theorem mem_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : (μ : ℂ) ∈ faceRegSet p h k J m μ := by
  refine ⟨hμ, fun i hi hden => ?_⟩
  have hi' := Finset.mem_sdiff.1 hi
  apply hi'.2
  refine mem_faceResSet.2 ⟨hi'.1, ?_⟩
  have := congrArg Complex.re hden
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.mul_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.zero_re, mul_zero, sub_zero, zero_mul] at this
  push_cast at this ⊢
  linarith

theorem faceRegSet_mem_nhds (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : faceRegSet p h k J m μ ∈ 𝓝 (μ : ℂ) :=
  (isOpen_faceRegSet p h k J m μ).mem_nhds (mem_faceRegSet p h k J m hμ)

/-- The holomorphic factor of the face `(J, m)` at `μ`: the regular factor times the
complementary chart zeta function of the face amplitude. -/
noncomputable def faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) (s : ℂ) : ℂ :=
  regularFactor h k J m μ s *
    chartZeta (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s

theorem differentiableOn_faceHolo (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) :
    DifferentiableOn ℂ (faceHolo p F h k J m μ) (faceRegSet p h k J m μ) := by
  obtain ⟨C, hC, hflat⟩ := flatOn_faceAmp p J hF hp0 hm
  refine DifferentiableOn.mul ?_ ?_
  · exact differentiableOn_regularFactor h k J m μ fun s hs => hs.2
  · exact (differentiableOn_chartZeta_flat (continuous_faceAmp p J hF m).continuousOn hC
      hflat _ _).mono fun s hs => flatStrip_subtype J hs.1

/-- The face sum at depth `p`, with every inner factor factorised at `μ`. -/
theorem chartZetaAtDepth_eq_faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (s : ℂ) :
    chartZetaAtDepth p F h k s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s) := by
  unfold chartZetaAtDepth faceHolo
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [innerFactor_eq_res h k x.1 x.2 μ s]
  ring

end Faces

/-! ### The polar coefficients and the principal part -/

section Polar

variable {d : ℕ}

/-- ★ **The chart polar coefficients at `μ`.**  `chartPolarCoeff p F h k μ q` is the coefficient
of `(s − μ)^{−(q+1)}` in the face sum at depth `p`: over the faces of pole order `c ≥ q + 1`, the
face weight times the resonant constant times `(−1)^c` times the Taylor coefficient of order
`c − 1 − q` of the holomorphic factor at `μ`. -/
noncomputable def chartPolarCoeff (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℂ :=
  ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ poleOrder h k x.1 x.2 μ),
    ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
      ((-1) ^ poleOrder h k x.1 x.2 μ *
        iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
          ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ))

/-- The polar coefficients vanish beyond the maximal pole order. -/
theorem chartPolarCoeff_eq_zero (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) {q : ℕ} (hq : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ < q + 1) :
    chartPolarCoeff p F h k μ q = 0 := by
  unfold chartPolarCoeff
  rw [Finset.filter_false_of_mem fun x hx => not_le.2 (hq x hx)]
  simp

/-- `μ` is a candidate pole at depth `p` iff some face has positive pole order. -/
theorem poleAt_iff_poleOrder (p h k : Fin d → ℕ) (μ : ℝ) :
    PoleAt p h k (μ : ℂ) ↔ ∃ x ∈ SmoothEngine.faceIndex p, 0 < poleOrder h k x.1 x.2 μ := by
  unfold PoleAt poleOrder
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi, hden⟩
    refine ⟨i, mem_faceResSet.2 ⟨hi, ?_⟩⟩
    have := congrArg Complex.re hden
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.mul_re,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.zero_re, mul_zero, sub_zero, zero_mul] at this
    push_cast at this ⊢
    linarith
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_faceResSet.1 hi).1, by
      rw [denom_eq_of_mem_faceResSet hi]; simp⟩

theorem chartPolarCoeff_eq_zero_of_not_poleAt (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ)
    (h k : Fin d → ℕ) {μ : ℝ} (hμ : ¬ PoleAt p h k (μ : ℂ)) (q : ℕ) :
    chartPolarCoeff p F h k μ q = 0 := by
  refine chartPolarCoeff_eq_zero p F h k μ fun x hx => ?_
  rw [poleAt_iff_poleOrder] at hμ
  push Not at hμ
  have := hμ x hx
  omega

/-- The principal part of one face, in the form produced by `pole_taylor_isBigO_one`. -/
theorem face_sub_principal_isBigO_one (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) :
    (fun s : ℂ => ((μ : ℂ) - s)⁻¹ ^ poleOrder h k J m μ * faceHolo p F h k J m μ s -
      ∑ q ∈ range (poleOrder h k J m μ),
        (-1) ^ poleOrder h k J m μ *
          iteratedDeriv (poleOrder h k J m μ - 1 - q) (faceHolo p F h k J m μ) μ /
            ((poleOrder h k J m μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1))
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  pole_taylor_isBigO_one (faceRegSet_mem_nhds p h k J m hμ)
    (differentiableOn_faceHolo p hF h k hp0 J hm μ) _

/-- Rearrangement of the principal part `polarPart D (chartPolarCoeff …) μ` as a sum over
faces, for `D + 1` at least every pole order. -/
theorem polarPart_chartPolarCoeff_eq (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) (s : ℂ) :
    polarPart D (chartPolarCoeff p F h k μ) μ s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
          (-1) ^ poleOrder h k x.1 x.2 μ *
            iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
              ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1) := by
  unfold polarPart chartPolarCoeff
  simp_rw [Finset.sum_div, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hrange : (range (D + 1)).filter (fun q => q + 1 ≤ poleOrder h k x.1 x.2 μ) =
      range (poleOrder h k x.1 x.2 μ) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hD x hx
    omega
  rw [hrange]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- ★★ **The face sum minus its principal part is bounded near `μ`.**  For `F` smooth, at a
positive depth `p` whose flat strip contains `μ`, and for `D + 1` at least every pole order at
`μ`, `chartZetaAtDepth p F h k − polarPart D (chartPolarCoeff p F h k μ) μ = O(1)` on a
punctured neighbourhood of `μ`.  This is the input form of `polarCoeff_unique`. -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart D (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have hrw : ∀ s : ℂ, chartZetaAtDepth p F h k s - polarPart D (chartPolarCoeff p F h k μ) μ s =
      ∑ x ∈ SmoothEngine.faceIndex p,
        ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
          (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s -
            ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
              (-1) ^ poleOrder h k x.1 x.2 μ *
                iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
                  ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1)) := by
    intro s
    rw [chartZetaAtDepth_eq_faceHolo p F h k μ s, polarPart_chartPolarCoeff_eq p F h k μ hD s,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have key : (∑ x ∈ SmoothEngine.faceIndex p, fun s : ℂ =>
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s -
          ∑ q ∈ range (poleOrder h k x.1 x.2 μ),
            (-1) ^ poleOrder h k x.1 x.2 μ *
              iteratedDeriv (poleOrder h k x.1 x.2 μ - 1 - q) (faceHolo p F h k x.1 x.2 μ) μ /
                ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1)))
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
    IsBigO.sum fun x hx => (face_sub_principal_isBigO_one p hF h k hp0 hμ x.1
      (Finset.mem_sigma.1 hx).2).const_mul_left _
  refine key.congr_left fun s => ?_
  rw [Finset.sum_apply, hrw]

/-- The same with the universal degree bound `D = d` (every pole order is at most `d`). -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one' (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart d (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  chartZetaAtDepth_sub_polarPart_isBigO_one p hF h k hp0 hμ fun x _ =>
    (poleOrder_le h k x.1 x.2 μ).trans (Nat.le_succ d)

/-- Away from the candidate poles the face sum is itself bounded near `μ`. -/
theorem chartZetaAtDepth_isBigO_one_of_not_poleAt (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) (hpole : ¬ PoleAt p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s) =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
  have := chartZetaAtDepth_sub_polarPart_isBigO_one' p hF h k hp0 hμ
  have hz : ∀ s : ℂ, polarPart d (chartPolarCoeff p F h k μ) μ s = 0 := fun s => by
    unfold polarPart
    simp [chartPolarCoeff_eq_zero_of_not_poleAt p F h k hpole]
  simpa [hz] using this

end Polar

/-! ### The canonical depth -/

section Depth

variable {d : ℕ}

/-- At the depth `depthOf h k L` with `L ≥ L₀ h`, every real `μ < L` lies in the flat strip. -/
theorem flatStrip_depthOf {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) : FlatStrip (depthOf h k L) h k (μ : ℂ) := by
  intro i
  have hadd : ((depthOf h k L i : ℕ) : ℝ) + h i = 2 * k i * L := by
    exact_mod_cast depthOf_add hk hL i
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  rw [Complex.ofReal_re, hadd]
  nlinarith

/-- ★ The principal part of the face sum at the canonical depth `depthOf h k L`, for any real
`μ < L` (no candidate-pole hypothesis: the polar coefficients vanish when `μ` is not a pole). -/
theorem chartZetaAtDepth_depthOf_sub_polarPart_isBigO_one {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) :
    (fun s : ℂ => chartZetaAtDepth (depthOf h k L) F h k s -
      polarPart d (chartPolarCoeff (depthOf h k L) F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) :=
  chartZetaAtDepth_sub_polarPart_isBigO_one' _ hF h k (depthOf_pos hk hL)
    (flatStrip_depthOf hk hL hμ)

end Depth

end Grammar
```

## Grammar/EmpiricalChartMellin.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CoupledChartZeta
import Grammar.EmpiricalGeneral
import Grammar.MellinTiltIntegrable
import Grammar.FluctuationComplex

/-!
# The Mellin transform of the empirical chart integral (route B, unit B10)

The empirical chart integral
`empIntegral η ζ h k N = ∫_{(0,1]^d} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)} dv`
has the Mellin transform

  `mellin (empIntegral η ζ h k) s = coupledChartZeta (fieldFam η ζ) h k s
                                  = ∫_0^∞ t^{s−1} e^{−t} chartZeta (η e^{√t ζ}) h k s dt`

on the initial strip `0 < Re s`, `2kᵢ Re s < hᵢ + 1` (★★ `mellin_empIntegral_eq_coupledChartZeta`).
The proof substitutes `N = t / v^{2k}` in the inner Mellin integral (`mellin_exp_tilt`, giving the
complex fluctuation function `S(s, ζ(v))`) after one Fubini interchange, then unfolds `S` and
interchanges again; both interchanges are justified by the AM–GM majorant `exp_tilt_le` and the
coupled envelope of `CoupledChartZeta`.  The two side conditions of `polarCoeff_unique` — local
integrability of the empirical integral on `(0, ∞)` and boundedness at `0⁺` — are derived from
`MellinTiltIntegrable` (`locallyIntegrableOn_empIntegral`, `empIntegral_isBigO_one_zero`).
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### Bounds on the closed box -/

section Bounds

theorem exists_abs_bound_closedBox {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ closedBox d 1, |η v| ≤ C := by
  obtain ⟨M, hM⟩ := exists_field_bound hη
  exact ⟨max M 0, le_max_right _ _, fun v hv => (hM v hv).trans (le_max_left _ _)⟩

theorem mem_closedBox_of_mem_box {v : Fin d → ℝ} (hv : v ∈ SmoothEngine.box (Fin d) 1) :
    v ∈ closedBox d 1 :=
  box_subset_closedBox' 1 hv

/-- The field family is flat of order `0` with exponential growth in the coupling. -/
theorem flatOn_fieldFam {η ζ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    ∃ C M : ℝ, 0 ≤ C ∧ ∀ τ, 0 ≤ τ →
      FlatOn (fieldFam η ζ τ) 0 (C * (1 + τ) ^ 0 * Real.exp (M * τ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  refine ⟨C, M, hC0, fun τ hτ v hv => ?_⟩
  have hv' := mem_closedBox_of_mem_box hv
  have hmono : mono (0 : Fin d → ℕ) v = 1 := by simp [mono]
  rw [hmono, mul_one, pow_zero, mul_one]
  unfold fieldFam
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (hC v hv') ?_ (Real.exp_pos _).le hC0
  rw [Real.exp_le_exp]
  calc τ * ζ v ≤ τ * |ζ v| := by gcongr; exact le_abs_self _
    _ ≤ τ * M := by gcongr; exact hM v hv'
    _ = M * τ := mul_comm _ _

end Bounds

/-! ### Pointwise identities on the box -/

section Pointwise

variable (h k : Fin d → ℕ)

theorem mono_two_mul_eq_sq (v : Fin d → ℝ) :
    mono (fun i => 2 * k i) v = mono k v ^ 2 := by
  unfold mono
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

theorem sqrt_mono_two_mul {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    Real.sqrt (mono (fun i => 2 * k i) v) = mono k v := by
  rw [mono_two_mul_eq_sq, Real.sqrt_sq (mono_pos k hv).le]

/-- `v^h (v^{2k})^{−s} = cpowWeight h k s v` on the positive box. -/
theorem mono_mul_cpow_neg {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) (s : ℂ) :
    ((mono h v : ℝ) : ℂ) * ((mono (fun i => 2 * k i) v : ℝ) : ℂ) ^ (-s) =
      cpowWeight h k s v := by
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have hmono : ∀ a : Fin d → ℕ, mono a v = Real.exp (logSum a v) := fun a => by
    unfold mono logSum
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Real.exp_nat_mul, Real.exp_log (hv i)]
  have hlog : Real.log (mono (fun i => 2 * k i) v) = 2 * logSum k v := by
    rw [hmono, Real.log_exp]
    unfold logSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hK.ne'), ← Complex.ofReal_log hK.le, hlog,
    hmono h, Complex.ofReal_exp, ← Complex.exp_add]
  unfold cpowWeight
  congr 1
  push_cast
  ring

end Pointwise

/-! ### The Mellin integrand of the empirical integral -/

section MellinIntegrand

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The empirical integrand in the paper's form. -/
noncomputable def empIntegrandFun (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  η v * mono h v * Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v)

theorem continuous_empIntegrandFun (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    Continuous fun z : ℝ × (Fin d → ℝ) => empIntegrandFun η ζ h k z.1 z.2 := by
  unfold empIntegrandFun
  refine ((hη.continuous.comp continuous_snd).mul ((continuous_mono h).comp continuous_snd)).mul
    (Real.continuous_exp.comp ?_)
  refine ((continuous_neg.comp continuous_fst).mul
    ((continuous_mono _).comp continuous_snd)).add ?_
  exact ((Real.continuous_sqrt.comp continuous_fst).mul
    ((continuous_mono k).comp continuous_snd)).mul (hζ.continuous.comp continuous_snd)

/-- The Mellin double integrand `N^{s−1} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)}`. -/
noncomputable def mellinEmpIntegrand (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (s : ℂ)
    (z : ℝ × (Fin d → ℝ)) : ℂ :=
  (z.1 : ℂ) ^ (s - 1) * (empIntegrandFun η ζ h k z.1 z.2 : ℂ)

theorem measurable_mellinEmpIntegrand (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (s : ℂ) :
    Measurable (mellinEmpIntegrand η ζ h k s) :=
  ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (Complex.measurable_ofReal.comp (continuous_empIntegrandFun hη hζ).measurable)

/-- The Mellin measure: Lebesgue measure on `(0,∞) × (0,1]^d`. -/
noncomputable def mellinMeasure (d : ℕ) : Measure (ℝ × (Fin d → ℝ)) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (SmoothEngine.box (Fin d) 1))

/-- The AM–GM majorant of the Mellin integrand at a fixed box point. -/
theorem norm_mellinEmpIntegrand_le {s : ℂ} {N : ℝ} (hN : 0 < N) {v : Fin d → ℝ}
    (hv : ∀ i, 0 < v i) {M : ℝ} (hζv : |ζ v| ≤ M) :
    ‖mellinEmpIntegrand η ζ h k s (N, v)‖ ≤
      |η v| * mono h v * Real.exp (M ^ 2 / 2) *
        (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) := by
  unfold mellinEmpIntegrand empIntegrandFun
  simp only
  rw [norm_cpow_mul_ofReal hN, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (mono_pos h hv)]
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have htilt := exp_tilt_le hK (mono k v * ζ v) hN.le
  have hH : (mono k v * ζ v) ^ 2 / (2 * mono (fun i => 2 * k i) v) = ζ v ^ 2 / 2 := by
    rw [mono_two_mul_eq_sq]
    have := (mono_pos k hv).ne'
    field_simp
  rw [hH] at htilt
  have hζ2 : Real.exp (ζ v ^ 2 / 2) ≤ Real.exp (M ^ 2 / 2) := by
    rw [Real.exp_le_exp]
    have := sq_abs (ζ v)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hζv
    nlinarith [abs_nonneg (ζ v)]
  have hN' : 0 ≤ N ^ (s.re - 1) := Real.rpow_nonneg hN.le _
  have hexp : Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v) ≤
      Real.exp (M ^ 2 / 2) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N) := by
    rw [mul_assoc (Real.sqrt N)]
    exact htilt.trans (mul_le_mul_of_nonneg_right hζ2 (Real.exp_pos _).le)
  have hηm : 0 ≤ |η v| * mono h v := mul_nonneg (abs_nonneg _) (mono_pos h hv).le
  calc N ^ (s.re - 1) * (|η v| * mono h v *
        Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v))
      ≤ N ^ (s.re - 1) * (|η v| * mono h v *
        (Real.exp (M ^ 2 / 2) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hηm) hN'
    _ = _ := by ring

/-- ★ **Absolute integrability of the Mellin double integral** on the initial strip. -/
theorem integrable_mellinEmpIntegrand (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {s : ℂ}
    (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    Integrable (mellinEmpIntegrand η ζ h k s) (mellinMeasure d) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, _, hM⟩ := exists_abs_bound_closedBox hζ
  have hmeas := (measurable_mellinEmpIntegrand (h := h) (k := k) hη hζ s).aestronglyMeasurable
    (μ := mellinMeasure d)
  unfold mellinMeasure
  rw [integrable_prod_iff' hmeas]
  constructor
  · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    refine Eventually.of_forall fun v hv => ?_
    have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
    have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv'
    have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1)
      (b := mono (fun i => 2 * k i) v / 2) (by linarith) one_pos (by positivity)).const_mul
      (|η v| * mono h v * Real.exp (M ^ 2 / 2))
    refine hint.mono' ((measurable_mellinEmpIntegrand hη hζ s).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun N hN => ?_
    have := norm_mellinEmpIntegrand_le (η := η) (ζ := ζ) (h := h) (k := k) (s := s) hN hv'
      (hM v (mem_closedBox_of_mem_box hv))
    simp only [Real.rpow_one] at this ⊢
    exact this
  · -- the inner integral is bounded by the population zeta integrand
    have hc : ∀ i, -1 < (h i : ℝ) + (-2 * (k i : ℝ) * s.re) := fun i => by linarith [hs i]
    have hbox : Integrable (fun v : Fin d → ℝ =>
        Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re) *
          ∏ i, v i ^ ((h i : ℝ) + (-2 * (k i : ℝ) * s.re)))
        (volume.restrict (SmoothEngine.box (Fin d) 1)) := by
      have := (integrableOn_prod_rpow_mul_log_pow hc (fun i => 2 * (k i : ℝ)) 0
        zero_le_one).const_mul (Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re))
      simp only [pow_zero, mul_one] at this
      exact this
    refine hbox.mono' ?_ ?_
    · exact ((measurable_mellinEmpIntegrand (h := h) (k := k) hη hζ
        s).norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
      refine Eventually.of_forall fun v hv => ?_
      have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
      have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv'
      have hvc := mem_closedBox_of_mem_box hv
      -- the majorant integral in `N`
      have hmaj : ∫ N in Ioi (0 : ℝ), |η v| * mono h v * Real.exp (M ^ 2 / 2) *
          (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) =
          |η v| * mono h v * Real.exp (M ^ 2 / 2) *
            ((mono (fun i => 2 * k i) v / 2) ^ (-s.re) * Real.Gamma s.re) := by
        rw [integral_const_mul]
        congr 1
        have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s.re - 1)
          (b := mono (fun i => 2 * k i) v / 2) one_pos (by linarith) (by positivity)
        simp only [Real.rpow_one, sub_add_cancel, div_one, mul_one] at this
        rw [this]
      have hint : IntegrableOn (fun N : ℝ => |η v| * mono h v * Real.exp (M ^ 2 / 2) *
          (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N))) (Ioi 0) := by
        refine IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_rpow
          (p := 1) (s := s.re - 1) (b := mono (fun i => 2 * k i) v / 2) (by linarith) one_pos
          (by positivity)) (|η v| * mono h v * Real.exp (M ^ 2 / 2))) (fun N _ => ?_)
          measurableSet_Ioi
        simp only [Real.rpow_one]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ N in Ioi (0 : ℝ), ‖mellinEmpIntegrand η ζ h k s (N, v)‖
          ≤ ∫ N in Ioi (0 : ℝ), |η v| * mono h v * Real.exp (M ^ 2 / 2) *
              (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
            exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun N hN =>
              norm_mellinEmpIntegrand_le hN hv' (hM v hvc))
        _ = |η v| * mono h v * Real.exp (M ^ 2 / 2) *
              ((mono (fun i => 2 * k i) v / 2) ^ (-s.re) * Real.Gamma s.re) := hmaj
        _ ≤ Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re) *
              ∏ i, v i ^ ((h i : ℝ) + (-2 * (k i : ℝ) * s.re)) := by
            have hG : 0 ≤ Real.Gamma s.re := Real.Gamma_nonneg_of_nonneg hs0.le
            have hpow : (mono (fun i => 2 * k i) v / 2) ^ (-s.re) =
                (1 / 2) ^ (-s.re) * ∏ i, v i ^ (-2 * (k i : ℝ) * s.re) := by
              rw [div_eq_mul_one_div, mul_comm, Real.mul_rpow (by norm_num) hK.le]
              congr 1
              unfold mono
              rw [← Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv' i).le _]
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [← Real.rpow_natCast, ← Real.rpow_mul (hv' i).le]
              congr 1
              push_cast
              ring
            rw [hpow, ← mono_mul_prod_rpow h _ hv']
            have hη' : |η v| ≤ Cη := hCη v hvc
            have hm0 : 0 ≤ mono h v := (mono_pos h hv').le
            have hP0 : 0 ≤ ∏ i, v i ^ (-2 * (k i : ℝ) * s.re) :=
              Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hv' i).le _
            have h20 : (0 : ℝ) ≤ (1 / 2) ^ (-s.re) := Real.rpow_nonneg (by norm_num) _
            have hX : 0 ≤ (1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) *
                Real.Gamma s.re :=
              mul_nonneg (mul_nonneg h20 hP0) hG
            calc |η v| * mono h v * Real.exp (M ^ 2 / 2) *
                  ((1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) * Real.Gamma s.re)
                ≤ Cη * mono h v * Real.exp (M ^ 2 / 2) *
                  ((1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) * Real.Gamma s.re) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hη' hm0) (Real.exp_pos _).le) hX
              _ = _ := by ring

end MellinIntegrand

/-! ### The Mellin identity -/

section Identity

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The inner Mellin integral at a box point: `∫_0^∞ N^{s−1} η v^h e^{−Nv^{2k}+√N v^k ζ} dN
= η(v) · cpowWeight h k s v · S(s, ζ(v))`. -/
theorem integral_mellinEmpIntegrand_eq {s : ℂ} {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    ∫ N in Ioi (0 : ℝ), mellinEmpIntegrand η ζ h k s (N, v) =
      (η v : ℂ) * cpowWeight h k s v * fluctuationCplx s (ζ v) := by
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have hfun : (fun N : ℝ => mellinEmpIntegrand η ζ h k s (N, v)) =
      fun N : ℝ => ((η v * mono h v : ℝ) : ℂ) * ((N : ℂ) ^ (s - 1) •
        (Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * (mono k v * ζ v)) : ℂ)) := by
    funext N
    unfold mellinEmpIntegrand empIntegrandFun
    simp only [smul_eq_mul]
    push_cast
    ring_nf
  rw [hfun, integral_const_mul]
  change ((η v * mono h v : ℝ) : ℂ) * mellin (fun N : ℝ =>
    (Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * (mono k v * ζ v)) : ℂ)) s = _
  rw [mellin_exp_tilt hK, sqrt_mono_two_mul k hv,
    mul_div_cancel_left₀ _ (mono_pos k hv).ne', Complex.ofReal_mul, mul_assoc,
    ← mul_assoc ((mono h v : ℝ) : ℂ), mono_mul_cpow_neg h k hv s, mul_assoc]

/-- The coupled integrand of the field family in the paper's form. -/
theorem coupIntegrand_fieldFam_zero (s : ℂ) (z : ℝ × (Fin d → ℝ)) :
    coupIntegrand (fieldFam η ζ) h k 0 s z =
      (η z.2 : ℂ) * cpowWeight h k s z.2 *
        ((z.1 : ℂ) ^ (s - 1) * (Real.exp (-z.1 + ζ z.2 * Real.sqrt z.1) : ℂ)) := by
  unfold coupIntegrand coupKernel fieldFam
  rw [Real.exp_add]
  push_cast
  ring_nf

/-- ★★ **The Mellin transform of the empirical chart integral is the coupled chart zeta
functional of the field family**, on the initial strip. -/
theorem mellin_empIntegral_eq_coupledChartZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    {s : ℂ} (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    mellin (fun N => (empIntegral η ζ h k N : ℂ)) s = coupledChartZeta (fieldFam η ζ) h k s := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_fieldFam hη hζ
  have hcont : Continuous fun z : ℝ × (Fin d → ℝ) => fieldFam η ζ z.1 z.2 :=
    (contDiff_fieldFam_joint hη hζ).continuous
  -- step 1: the Mellin transform as a double integral, and the first interchange
  have h1 : mellin (fun N => (empIntegral η ζ h k N : ℂ)) s =
      ∫ v in SmoothEngine.box (Fin d) 1, ∫ N in Ioi (0 : ℝ),
        mellinEmpIntegrand η ζ h k s (N, v) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
      (f := fun N v => mellinEmpIntegrand η ζ h k s (N, v))
      (integrable_mellinEmpIntegrand hη hζ hs0 hs)
    rw [← hswap]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun N _ => ?_
    beta_reduce
    rw [empIntegral_eq, ← integral_complex_ofReal, smul_eq_mul, ← integral_const_mul]
    rfl
  -- step 2: the inner integrals
  have h2 : ∫ v in SmoothEngine.box (Fin d) 1, ∫ N in Ioi (0 : ℝ),
      mellinEmpIntegrand η ζ h k s (N, v) =
      ∫ v in SmoothEngine.box (Fin d) 1, ∫ t in Ioi (0 : ℝ),
        coupIntegrand (fieldFam η ζ) h k 0 s (t, v) := by
    refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v hv => ?_
    have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
    rw [integral_mellinEmpIntegrand_eq hv']
    unfold fluctuationCplx
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [coupIntegrand_fieldFam_zero]
  -- step 3: the second interchange
  have hint := integrable_coupIntegrand hcont hC hflat h k 0 hs0 hs.flatStrip
  have h3 : ∫ v in SmoothEngine.box (Fin d) 1, ∫ t in Ioi (0 : ℝ),
      coupIntegrand (fieldFam η ζ) h k 0 s (t, v) = coupledLogMoment (fieldFam η ζ) h k 0 s := by
    unfold coupledLogMoment coupMeasure
    rw [integral_prod _ hint]
    exact (integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
      (f := fun t v => coupIntegrand (fieldFam η ζ) h k 0 s (t, v)) hint).symm
  rw [h1, h2, h3, coupledChartZeta_eq_logMoment_zero hcont hC hflat h k hs0 hs.flatStrip]

end Identity

/-! ### Local integrability and boundedness at the origin -/

section Regularity

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

theorem measurableSet_closedBox (b : ℝ) : MeasurableSet (closedBox d b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

instance isFiniteMeasure_restrict_box :
    IsFiniteMeasure (volume.restrict (SmoothEngine.box (Fin d) 1)) :=
  isFiniteMeasure_restrict.2 (volume_box_lt_top 1).ne

/-- The empirical integral as a tilt integral with globally bounded data. -/
theorem empIntegral_eq_integral_tilt (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral η ζ h k N = ∫ v, (closedBox d 1).indicator (fun v => η v * mono h v) v *
      Real.exp (-N * mono (fun i => 2 * k i) v +
        Real.sqrt N * (closedBox d 1).indicator (fun v => mono k v * ζ v) v)
      ∂(volume.restrict (SmoothEngine.box (Fin d) 1)) := by
  rw [empIntegral_eq]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v hv => ?_
  have hv' := mem_closedBox_of_mem_box hv
  simp only [Set.indicator_of_mem hv']
  ring_nf

theorem abs_indicator_le {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ v ∈ closedBox d 1, |f v| ≤ C) (v : Fin d → ℝ) :
    |(closedBox d 1).indicator f v| ≤ C := by
  by_cases hv : v ∈ closedBox d 1
  · rw [Set.indicator_of_mem hv]; exact hf v hv
  · rw [Set.indicator_of_notMem hv, abs_zero]; exact hC

theorem mono_le_one_closedBox (a : Fin d → ℕ) {v : Fin d → ℝ} (hv : v ∈ closedBox d 1) :
    mono a v ≤ 1 :=
  Finset.prod_le_one (fun i _ => pow_nonneg ((mem_closedBox.1 hv i).1) _)
    fun i _ => pow_le_one₀ ((mem_closedBox.1 hv i).1) ((mem_closedBox.1 hv i).2)

theorem mono_nonneg_closedBox (a : Fin d → ℕ) {v : Fin d → ℝ} (hv : v ∈ closedBox d 1) :
    0 ≤ mono a v :=
  Finset.prod_nonneg fun i _ => pow_nonneg ((mem_closedBox.1 hv i).1) _

/-- ★ The empirical integral is locally integrable on `(0, ∞)`. -/
theorem locallyIntegrableOn_empIntegral (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    LocallyIntegrableOn (fun N => (empIntegral η ζ h k N : ℂ)) (Ioi 0) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  have hobs : ∀ v, |(closedBox d 1).indicator (fun v => η v * mono h v) v| ≤ Cη :=
    abs_indicator_le hCη0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox h hv)]
      calc |η v| * mono h v ≤ Cη * 1 :=
            mul_le_mul (hCη v hv) (mono_le_one_closedBox h hv) (mono_nonneg_closedBox h hv) hCη0
        _ = Cη := mul_one _
  have hΞ : ∀ v, |(closedBox d 1).indicator (fun v => mono k v * ζ v) v| ≤ M :=
    abs_indicator_le hM0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox k hv)]
      calc mono k v * |ζ v| ≤ 1 * M :=
            mul_le_mul (mono_le_one_closedBox k hv) (hM v hv) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
  have hK : ∀ᵐ v ∂(volume.restrict (SmoothEngine.box (Fin d) 1)),
      0 ≤ mono (fun i => 2 * k i) v := by
    rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    exact Eventually.of_forall fun v hv => (mono_pos _ fun i => SmoothEngine.pos_of_mem_box hv i).le
  have := locallyIntegrableOn_integral_tilt (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
    (continuous_mono _).measurable
    (((continuous_mono k).mul hζ.continuous).measurable.indicator (measurableSet_closedBox 1))
    ((hη.continuous.mul (continuous_mono h)).measurable.indicator (measurableSet_closedBox 1))
    hK hΞ hobs
  have hfun : (fun N => (empIntegral η ζ h k N : ℂ)) = fun N =>
      ((∫ v, (closedBox d 1).indicator (fun v => η v * mono h v) v *
        Real.exp (-N * mono (fun i => 2 * k i) v +
          Real.sqrt N * (closedBox d 1).indicator (fun v => mono k v * ζ v) v)
        ∂(volume.restrict (SmoothEngine.box (Fin d) 1)) : ℝ) : ℂ) := by
    funext N
    rw [empIntegral_eq_integral_tilt]
  rw [hfun]
  exact this

/-- ★ The empirical integral is bounded at `0⁺`. -/
theorem empIntegral_isBigO_one_zero (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    (fun N => (empIntegral η ζ h k N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  have hobs : ∀ v, |(closedBox d 1).indicator (fun v => η v * mono h v) v| ≤ Cη :=
    abs_indicator_le hCη0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox h hv)]
      calc |η v| * mono h v ≤ Cη * 1 :=
            mul_le_mul (hCη v hv) (mono_le_one_closedBox h hv) (mono_nonneg_closedBox h hv) hCη0
        _ = Cη := mul_one _
  have hΞ : ∀ v, |(closedBox d 1).indicator (fun v => mono k v * ζ v) v| ≤ M :=
    abs_indicator_le hM0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox k hv)]
      calc mono k v * |ζ v| ≤ 1 * M :=
            mul_le_mul (mono_le_one_closedBox k hv) (hM v hv) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
  have hK : ∀ᵐ v ∂(volume.restrict (SmoothEngine.box (Fin d) 1)),
      0 ≤ mono (fun i => 2 * k i) v := by
    rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    exact Eventually.of_forall fun v hv => (mono_pos _ fun i => SmoothEngine.pos_of_mem_box hv i).le
  have := integral_tilt_isBigO_one (ν := volume.restrict (SmoothEngine.box (Fin d) 1)) hK hΞ hobs
  refine this.congr_left fun N => ?_
  rw [empIntegral_eq_integral_tilt]

end Regularity

end Grammar
```

## Grammar/EmpiricalCouplingAllLog.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CoupledPolarInterchange

/-!
# The empirical all-log formula in coupling-average form (route B, unit B13b)

The integrated polar coefficients of unit B12 are rearranged into the coupling average of the
population polar coefficients of the tilted amplitudes `η e^{√t ζ}` (Astra #168, (B4)):

  ★★★ `empIntegratedPolarCoeff_eq_couplingPolarCoeff`:
  `empIntegratedPolarCoeff p η ζ h k μ q
     = Σ_{j ∈ Ico q d} ((j−q)!)⁻¹ ∫_0^∞ t^{μ−1} (log t)^{j−q} e^{−t}
         chartPolarCoeff p (η e^{√t ζ}) h k μ j dt`

(`couplingPolarCoeff`), hence (B12) for lattice points `0 < μ < L`, `q ≤ d − 1`,

  ★★★ `ofReal_empCoeff_eq_couplingPolarCoeff`:
  `empCoeff η ζ h k μ q = (−1)^{q+1}/q! · couplingPolarCoeff (depthOf h k L) η ζ h k μ q`.

The proof is the normalised Taylor-coefficient convolution: per face `x = (J, m)` with holomorphic
factors `R_x = regularFactor` and `Φ_x = coupledFaceZeta`, the Taylor coefficients of `Φ_x` at `μ`
are the binomially split log moments (unit B13a and the derivative identity of unit B9), those of
`R_x · Φ_x` and of `R_x · ζ_{x,t}` (`ζ_{x,t} = chartZeta (faceAmp p J (η e^{√tζ}) m)`) are Cauchy
products (`taylorCoeff_mul`), so that

  `taylorCoeff (R_x Φ_x) μ n
     = Σ_{a ≤ n} (a!)⁻¹ ∫_0^∞ t^{μ−1}e^{−t}(log t)^a taylorCoeff (R_x ζ_{x,t}) μ (n−a) dt`

(`taylorCoeff_empFaceHolo_eq`), and the face sum with `n = c_x − 1 − q` regroups over `j = q + a`
into the population coefficients `chartPolarCoeff … j` inside the `t`-integral.  For `ζ = 0` the
inner coefficient is `t`-independent and the `t`-integrals are `Γ^{(j−q)}(μ)`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

variable {d : ℕ}

section Face

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-! ### Taylor coefficients of the face factors -/

/-- The Taylor coefficients of a coupled face zeta function are the split log moments. -/
theorem taylorCoeff_coupledFaceZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (n : ℕ) :
    taylorCoeff (coupledFaceZeta p η ζ h k J m) μ n = ∑ a ∈ range (n + 1),
      ((a ! : ℂ)⁻¹ * ((n - a)! : ℂ)⁻¹) *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
          chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
            (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - a) μ := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  unfold taylorCoeff coupledFaceZeta
  rw [iteratedDeriv_coupledChartZeta hcont hC (hflat J m hm) _ _ n hμ0' hμ',
    coupledLogMoment_eq_sum hcont hC (hflat J m hm) _ _ n hμ0' hμ', Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hfac : (n.choose a : ℂ) * (a ! : ℂ) * ((n - a)! : ℂ) = (n ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial han
  have ha0 : (a ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hna0 : ((n - a)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - a)
  have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hch : (n.choose a : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos han).ne'
  rw [← hfac]
  field_simp

/-- The Taylor coefficients of the chart zeta function of a tilted face amplitude are its box
log moments. -/
theorem taylorCoeff_chartZeta_faceAmp (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) (n : ℕ) :
    taylorCoeff (chartZeta (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
      (fun i : {i // ¬ inJ J i} => h i) (fun i => k i)) μ n =
      chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
        (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) n μ / (n ! : ℂ) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hτ : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hC' : 0 ≤ C * (1 + Real.sqrt t) ^ (∑ i, p i) * Real.exp (M * Real.sqrt t) := by positivity
  unfold taylorCoeff
  rw [iteratedDeriv_chartZeta_eq_logMoment
    (continuous_faceAmp p J (contDiff_fieldFam hη hζ _) m).continuousOn hC'
    (hflat J m hm _ hτ) _ _ n (flatStrip_subtype J hμ)]

theorem analyticAt_regularFactor (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : AnalyticAt ℂ (regularFactor h k J m μ) (μ : ℂ) :=
  (differentiableOn_regularFactor h k J m μ fun _ hs => hs.2).analyticAt
    (faceRegSet_mem_nhds p h k J m hμ)

theorem analyticAt_coupledFaceZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) : AnalyticAt ℂ (coupledFaceZeta p η ζ h k J m) (μ : ℂ) :=
  (differentiableOn_coupledFaceZeta hη hζ p hp0 h k J hm).analyticAt
    ((isOpen_posFlatStrip p h k).mem_nhds ⟨by simpa using hμ0, hμ⟩)

theorem analyticAt_chartZeta_faceAmp (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) :
    AnalyticAt ℂ (chartZeta (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
      (fun i : {i // ¬ inJ J i} => h i) (fun i => k i)) (μ : ℂ) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hτ : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hC' : 0 ≤ C * (1 + Real.sqrt t) ^ (∑ i, p i) * Real.exp (M * Real.sqrt t) := by positivity
  exact (differentiableOn_chartZeta_flat
    (continuous_faceAmp p J (contDiff_fieldFam hη hζ _) m).continuousOn hC' (hflat J m hm _ hτ)
    _ _).analyticAt ((FlatStrip.isOpen _ _ _).mem_nhds (flatStrip_subtype J hμ))

/-- The Taylor coefficients of the population face factor `faceHolo` of a tilted amplitude. -/
theorem taylorCoeff_faceHolo_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) (n : ℕ) :
    taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n =
      ∑ i ∈ range (n + 1), taylorCoeff (regularFactor h k J m μ) μ i *
        (chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
          (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - i) μ / ((n - i)! : ℂ)) := by
  have := taylorCoeff_mul (analyticAt_regularFactor p J m hμ)
    (analyticAt_chartZeta_faceAmp hη hζ p hp0 J hm hμ t) n
  unfold faceHolo
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [taylorCoeff_chartZeta_faceAmp hη hζ p hp0 J hm hμ t]

/-- Integrability of the coupling kernel with a log power against the Taylor coefficients of the
tilted face factors. -/
theorem integrable_coupKernel_logpow_mul_taylorCoeff_faceHolo (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d))
    {m : Fin d → ℕ} (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (a n : ℕ) :
    Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n)
      (volume.restrict (Ioi 0)) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n) =
      fun t => ∑ i ∈ range (n + 1), (taylorCoeff (regularFactor h k J m μ) μ i / ((n - i)! : ℂ)) *
        (coupKernel μ t * (Real.log t : ℂ) ^ a *
          chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
            (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - i) μ) := by
    funext t
    rw [taylorCoeff_faceHolo_eq hη hζ p hp0 J hm hμ t n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_coupKernel_logpow_mul_logMoment hcont hC (hflat J m hm) _ _ a (n - i) hμ0'
      hμ').const_mul _

/-- ★★ **The Taylor coefficients of the empirical face factor are the coupling averages of those
of the population face factors of the tilted amplitudes.** -/
theorem taylorCoeff_empFaceHolo_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (n : ℕ) :
    taylorCoeff (empFaceHolo p η ζ h k J m μ) μ n = ∑ a ∈ range (n + 1), (a ! : ℂ)⁻¹ *
      ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
        taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  -- abbreviations
  set R := fun i => taylorCoeff (regularFactor h k J m μ) μ i with hR
  set LM := fun (t : ℝ) (j : ℕ) => chartZetaLogMoment
    (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
    (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) j μ with hLM
  have hint : ∀ a j : ℕ, Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a * LM t j)
      (volume.restrict (Ioi 0)) := fun a j =>
    integrable_coupKernel_logpow_mul_logMoment hcont hC (hflat J m hm) _ _ a j hμ0' hμ'
  -- the left-hand side by Leibniz and the split log moments
  have hL : taylorCoeff (empFaceHolo p η ζ h k J m μ) μ n =
      ∑ i ∈ range (n + 1), ∑ a ∈ range (n - i + 1), R i * ((a ! : ℂ)⁻¹ * ((n - i - a)! : ℂ)⁻¹) *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - i - a) := by
    unfold empFaceHolo
    rw [taylorCoeff_mul (analyticAt_regularFactor p J m hμ)
      (analyticAt_coupledFaceZeta hη hζ p hp0 J hm hμ0 hμ) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [taylorCoeff_coupledFaceZeta hη hζ p hp0 J hm hμ0 hμ (n - i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  -- the right-hand side by Leibniz for the population factors
  have hRt : ∀ a : ℕ, (∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a)) =
      ∑ i ∈ range (n - a + 1), R i * ((n - a - i)! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - a - i) := by
    intro a
    have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
        taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a)) =
        fun t => ∑ i ∈ range (n - a + 1), R i * ((n - a - i)! : ℂ)⁻¹ *
          (coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - a - i)) := by
      funext t
      rw [taylorCoeff_faceHolo_eq hη hζ p hp0 J hm hμ t (n - a), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hR, hLM]
      ring
    rw [hfun, integral_finsetSum _ fun i _ => (hint a (n - a - i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  simp_rw [hRt, Finset.mul_sum]
  rw [hL]
  -- interchange the double sum over `i + a ≤ n`
  rw [Finset.sum_comm' (t' := range (n + 1)) (s' := fun a => range (n - a + 1))
    (fun i a => by
      simp only [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun i hi => ?_
  have hia : n - i - a = n - a - i := by omega
  rw [hia]
  ring

end Face

/-! ### The coupling-average polar coefficients -/

section Coupling

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★ **The coupling-average polar coefficients** (B4, zero-based):
`Σ_{j ∈ Ico q d} ((j−q)!)⁻¹ ∫_0^∞ t^{μ−1}(log t)^{j−q} e^{−t}
   chartPolarCoeff p (η e^{√tζ}) h k μ j dt`. -/
noncomputable def couplingPolarCoeff (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico q d, ((j - q)! : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
      chartPolarCoeff p (fieldFam η ζ (Real.sqrt t)) h k μ j

/-- The population polar coefficient of a tilted amplitude, written with `taylorCoeff`. -/
theorem chartPolarCoeff_fieldFam_eq (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (t : ℝ) (j : ℕ) :
    chartPolarCoeff p (fieldFam η ζ (Real.sqrt t)) h k μ j =
      ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ poleOrder h k x.1 x.2 μ),
        ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
          ((-1) ^ poleOrder h k x.1 x.2 μ *
            taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k x.1 x.2 μ) μ
              (poleOrder h k x.1 x.2 μ - 1 - j)) := by
  unfold chartPolarCoeff taylorCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- ★★★ **The integrated polar coefficients are the coupling averages of the population polar
coefficients of the tilted amplitudes** (B4). -/
theorem empIntegratedPolarCoeff_eq_couplingPolarCoeff (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (q : ℕ) :
    empIntegratedPolarCoeff p η ζ h k μ q = couplingPolarCoeff p η ζ h k μ q := by
  -- per-face data
  set c := fun x : (Σ _ : Finset (Fin d), Fin d → ℕ) => poleOrder h k x.1 x.2 μ with hc
  set w := fun x : (Σ _ : Finset (Fin d), Fin d → ℕ) =>
    ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ with hw
  set T := fun (x : (Σ _ : Finset (Fin d), Fin d → ℕ)) (t : ℝ) (n : ℕ) =>
    taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k x.1 x.2 μ) μ n with hT
  have hintT : ∀ x ∈ SmoothEngine.faceIndex p, ∀ a n : ℕ,
      Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a * T x t n)
        (volume.restrict (Ioi 0)) := fun x hx a n =>
    integrable_coupKernel_logpow_mul_taylorCoeff_faceHolo hη hζ p hp0 x.1
      (Finset.mem_sigma.1 hx).2 hμ0 hμ a n
  -- the left-hand side as a double sum over faces and `a < c x − q`
  have hL : empIntegratedPolarCoeff p η ζ h k μ q =
      ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
        ∑ a ∈ range (c x - q), w x * (-1) ^ c x * (a ! : ℂ)⁻¹ *
          ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * T x t (c x - 1 - q - a) := by
    have hL0 : empIntegratedPolarCoeff p η ζ h k μ q =
        ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
          w x * (-1) ^ c x * taylorCoeff (empFaceHolo p η ζ h k x.1 x.2 μ) μ (c x - 1 - q) := by
      unfold empIntegratedPolarCoeff finiteFacePolarCoeff taylorCoeff
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hw, hc]
      ring
    rw [hL0]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_filter.1 hx)
    have hqc : q + 1 ≤ c x := hx'.2
    have hrange : range (c x - 1 - q + 1) = range (c x - q) := by congr 1; omega
    rw [taylorCoeff_empFaceHolo_eq hη hζ p hp0 x.1 (Finset.mem_sigma.1 hx'.1).2 hμ0 hμ
      (c x - 1 - q), hrange, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hT]
    ring
  -- the right-hand side as a double sum over `j` and faces
  have hR : couplingPolarCoeff p η ζ h k μ q =
      ∑ j ∈ Finset.Ico q d, ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
        w x * (-1) ^ c x * ((j - q)! : ℂ)⁻¹ *
          ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
            T x t (c x - 1 - j) := by
    unfold couplingPolarCoeff
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [chartPolarCoeff_fieldFam_eq]
    have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
        ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
          w x * ((-1) ^ c x * T x t (c x - 1 - j))) =
        fun t => ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
          w x * (-1) ^ c x * (coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
            T x t (c x - 1 - j)) := by
      funext t
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hfun, integral_finsetSum _ fun x hx =>
      (hintT x (Finset.mem_filter.1 hx).1 (j - q) (c x - 1 - j)).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul]
    ring
  rw [hL, hR]
  -- reindex the inner sum of the left-hand side by `j = q + a`
  have hL' : ∀ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
      (∑ a ∈ range (c x - q), w x * (-1) ^ c x * (a ! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * T x t (c x - 1 - q - a)) =
      ∑ j ∈ Finset.Ico q (c x), w x * (-1) ^ c x * ((j - q)! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) * T x t (c x - 1 - j) := by
    intro x _
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : q + a - q = a := by omega
    have h2 : c x - 1 - (q + a) = c x - 1 - q - a := by omega
    rw [h1, h2]
  rw [Finset.sum_congr rfl hL']
  -- interchange the sums over faces and `j`
  refine Finset.sum_comm' fun x j => ?_
  simp only [Finset.mem_filter, Finset.mem_Ico]
  have hcd : c x ≤ d := poleOrder_le h k x.1 x.2 μ
  exact ⟨fun ⟨⟨hx, h1⟩, h2, h3⟩ => ⟨⟨hx, by omega⟩, h2, by omega⟩,
    fun ⟨⟨hx, h1⟩, h2, h3⟩ => ⟨⟨hx, by omega⟩, h2, by omega⟩⟩

/-- ★★★ **The empirical all-log formula in coupling-average form**: for lattice points
`0 < μ < L` and `q ≤ d − 1`,
`empCoeff η ζ h k μ q = (−1)^{q+1}/q! · couplingPolarCoeff (depthOf h k L) η ζ h k μ q`. -/
theorem ofReal_empCoeff_eq_couplingPolarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    (empCoeff η ζ h k μ q : ℂ) =
      (-1) ^ (q + 1) * couplingPolarCoeff (depthOf h k L) η ζ h k μ q / (q ! : ℂ) := by
  rw [ofReal_empCoeff_eq_empIntegratedPolarCoeff hη hζ hk hL hμlat hμL hμ0 hq,
    empIntegratedPolarCoeff_eq_couplingPolarCoeff hη hζ _ (depthOf_pos hk hL) hμ0
      (flatStrip_depthOf hk hL hμL)]

/-- The coupling-average coefficients are the polar data of the empirical coefficients. -/
theorem couplingPolarCoeff_eq_polarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    couplingPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q := by
  rw [← empIntegratedPolarCoeff_eq_couplingPolarCoeff hη hζ _ (depthOf_pos hk hL) hμ0
    (flatStrip_depthOf hk hL hμL)]
  exact empIntegratedPolarCoeff_eq_polarCoeff hη hζ hk hL hμlat hμL hμ0 hq

end Coupling

end Grammar
```

## Grammar/PolarTwoDimExamples.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalCouplingAllLog
import Grammar.LogExampleTwoDim

/-!
# Regression of the coupling-average formula against the `x²y²` example (unit 14)

Two general determination lemmas and one worked example.

* `chartZetaAtDepth_eventuallyEq_of_eqOn_strip`: the meromorphic face sum is determined by the
  strip values of the chart zeta functional — if a function `g` holomorphic on the strip
  `−1 < Re s < flatEdge` minus a finite set agrees with `chartZeta F h k` on the initial strip,
  then it agrees with `chartZetaAtDepth p F h k` on a punctured neighbourhood of every `μ` in the
  flat strip (identity theorem, as in `chartZetaAtDepth_eq_of_depths`).
* `chartPolarCoeff_eq_of_eventuallyEq`: the chart polar coefficients are the principal-part
  coefficients of any such local representative (`polarPart_eq_of_sub_isBigO_one`).

The example is the paper's `x²y²` chart on the unit square with a constant amplitude and a
constant field `a`: `chartZeta c 0 (1,1) s = c/(1−2s)² = (c/4)/(s−½)²`, so at `μ = ½` the polar
coefficients are `c/4` (order two) and `0` (order one); the coupling-average formula (B4) then
gives

  `empCoeff 1 a 0 (1,1) ½ 1 = S_{½}(a)/4`,  `empCoeff 1 a 0 (1,1) ½ 0 = −∂_ν S_ν(a)|_{½} / 4`

(★★ `empCoeff_xy_sq_one`, `empCoeff_xy_sq_zero`), exactly the constants of the independently
proved asymptotic `tendsto_logExample` of `LogExampleTwoDim`
(`4√n ∫∫ e^{−n x²y² + a√n xy} − (log n · S_{½}(a) − ∂_ν S_ν(a)|_{½}) → 0`), restated as
★ `tendsto_logExample_empCoeff`.  For `a = 0` these are `√π/4` and `−Γ'(½)/4`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Determination of the face sum by its strip values -/

section Determination

variable {d : ℕ} [Nonempty (Fin d)]

/-- ★ **The face sum is determined by the strip values of the chart zeta functional.** -/
theorem chartZetaAtDepth_eventuallyEq_of_eqOn_strip (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hp0 : ∀ i, 0 < p i)
    {g : ℂ → ℂ} {P' : Set ℂ} (hP' : P'.Finite)
    (hg : DifferentiableOn ℂ g ({s : ℂ | -1 < s.re ∧ s.re < flatEdge p h k} \ P'))
    (hseed : ∀ s : ℂ, ZetaStrip h k s → s ∉ P' → chartZeta F h k s = g s)
    (hseed' : ((-1 / 2 : ℝ) : ℂ) ∉ P') {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ)) (hμ1 : -1 < μ) :
    chartZetaAtDepth p F h k =ᶠ[𝓝[≠] (μ : ℂ)] g := by
  set P : Set ℂ := {t | PoleAt p h k t} ∪ P' with hP
  set U : Set ℂ := {t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ P with hU
  have hPfin : P.Finite := (finite_poleSet p h k hk).union hP'
  have hUopen : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin.isClosed
  have hUsub : ∀ t ∈ U, FlatStrip p h k t ∧ ¬ PoleAt p h k t := fun t ht =>
    ⟨(flatStrip_iff_re_lt p h k hk t).2 ht.1.2, fun hp => ht.2 (Or.inl hp)⟩
  have hf : AnalyticOnNhd ℂ (chartZetaAtDepth p F h k) U :=
    ((differentiableOn_chartZetaAtDepth p hF h k hp0).mono hUsub).analyticOnNhd hUopen
  have hg' : AnalyticOnNhd ℂ g U :=
    (hg.mono fun t ht => ⟨ht.1, fun hp => ht.2 (Or.inr hp)⟩).analyticOnNhd hUopen
  have hLpos : 0 < flatEdge p h k := flatEdge_pos p h k hk
  have hconn : IsPreconnected U := isPreconnected_strip_diff_finite (by linarith) hPfin
  have hz₀ : ((-1 / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨⟨by simp; norm_num, by simp; linarith⟩, ?_⟩
    rintro (hp | hp)
    · have := pos_re_of_poleAt hk hp; simp at this; linarith
    · exact hseed' hp
  have hfg : chartZetaAtDepth p F h k =ᶠ[𝓝 ((-1 / 2 : ℝ) : ℂ)] g := by
    filter_upwards [(ZetaStrip.isOpen h k).mem_nhds (zetaStrip_neg_half h k),
      hP'.isClosed.isOpen_compl.mem_nhds hseed'] with t ht ht'
    rw [chartZetaAtDepth_eq_chartZeta p hF h k ht, hseed t ht ht']
  have hEq : EqOn (chartZetaAtDepth p F h k) g U :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg' hconn hz₀ hfg
  -- a punctured neighbourhood of `μ` lies in `U`
  have hPfin' : (P \ {(μ : ℂ)}).Finite := hPfin.sdiff
  have hopen : IsOpen ({t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ (P \ {(μ : ℂ)})) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin'.isClosed
  have hmem : (μ : ℂ) ∈ {t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ (P \ {(μ : ℂ)}) :=
    ⟨⟨by simpa using hμ1, by simpa using (flatStrip_iff_re_lt p h k hk _).1 hμ⟩,
      fun hp => hp.2 rfl⟩
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin] with t ht htμ
  exact hEq ⟨ht.1, fun hp => ht.2 ⟨hp, htμ⟩⟩

end Determination

section Coefficients

variable {d : ℕ}

/-- ★ **The chart polar coefficients are the principal-part coefficients of any local
representative.** -/
theorem chartPolarCoeff_eq_of_eventuallyEq (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) {g : ℂ → ℂ}
    {a : ℕ → ℂ} (hg : chartZetaAtDepth p F h k =ᶠ[𝓝[≠] (μ : ℂ)] g)
    (ha : (fun s => g s - polarPart D a (μ : ℂ) s) =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, chartPolarCoeff p F h k μ q = a q := by
  have h1 := chartZetaAtDepth_sub_polarPart_isBigO_one p hF h k hp0 hμ hD
  have h2 : (fun s => g s - polarPart D (chartPolarCoeff p F h k μ) (μ : ℂ) s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
    refine h1.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hg] with s hs
    rw [hs]
  have h3 := ha.sub h2
  intro q hq
  refine polarPart_eq_of_sub_isBigO_one (D := D) (a := chartPolarCoeff p F h k μ) (b := a)
    (h3.congr_left fun s => ?_) q hq
  ring

end Coefficients

/-! ### The `x²y²` chart with a constant amplitude -/

section Example

/-- The polar coefficients of a constant amplitude `c` on the `x²y²` unit square at `μ = ½`:
`c/4` at order two and `0` at order one (for every positive depth whose flat strip contains `½`,
with `D = 1`). -/
theorem chartPolarCoeff_const_xy_sq (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p 0 (fun _ => 1) ((1 / 2 : ℝ) : ℂ)) {F : (Fin 2 → ℝ) → ℝ} {c : ℝ}
    (hFc : ∀ v, F v = c) :
    chartPolarCoeff p F 0 (fun _ => 1) (1 / 2) 1 = (c : ℂ) / 4 ∧
      chartPolarCoeff p F 0 (fun _ => 1) (1 / 2) 0 = 0 := by
  have hF : ContDiff ℝ ∞ F := by
    have : F = fun _ => c := funext hFc
    rw [this]; exact contDiff_const
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  set g : ℂ → ℂ := fun s => (c : ℂ) / (1 - 2 * s) ^ 2 with hgdef
  -- the strip values
  have hseed : ∀ s : ℂ, ZetaStrip (0 : Fin 2 → ℕ) (fun _ => 1) s →
      s ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) → chartZeta F 0 (fun _ => 1) s = g s := by
    intro s hs _
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      have hs0 := hs 0
      simp at this hs0
      linarith
    unfold chartZeta
    have hpt : ∀ u, (F u : ℂ) * cpowWeight 0 (fun _ => 1) s u =
        (c : ℂ) * cpowWeight 0 (fun _ => 1) s u := fun u => by rw [hFc]
    simp_rw [hpt]
    rw [integral_const_mul, integral_box_cpowWeight _ _ hs]
    simp only [hgdef, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply,
      Nat.cast_zero, Nat.cast_one]
    rw [div_pow, one_pow, mul_one_div]
    congr 1
    ring
  have hg : DifferentiableOn ℂ g
      ({s : ℂ | -1 < s.re ∧ s.re < flatEdge p 0 (fun _ => 1)} \ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ)) := by
    refine (differentiableOn_const _).div
      (((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).pow _)
      fun s hs => ?_
    refine pow_ne_zero _ fun h0 => hs.2 ?_
    have : s = ((1 / 2 : ℝ) : ℂ) := by push_cast; linear_combination -h0 / 2
    simp [this]
  have hseed' : ((-1 / 2 : ℝ) : ℂ) ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) := by
    norm_num [Set.mem_singleton_iff, Complex.ofReal_inj]
  have hev := chartZetaAtDepth_eventuallyEq_of_eqOn_strip p hF 0 (fun _ => 1) hk hp0
    (Set.finite_singleton _) hg hseed hseed' hμ (by norm_num)
  -- the principal part of `g` at `½`
  set a : ℕ → ℂ := fun q => if q = 1 then (c : ℂ) / 4 else 0 with hadef
  have ha : (fun s => g s - polarPart 1 a ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)]
      fun _ => (1 : ℂ) := by
    refine (isBigO_refl (fun _ : ℂ => (0 : ℂ)) _).congr' ?_ (EventuallyEq.refl _ _) |>.trans
      (isBigO_zero _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := by
      intro h0
      apply hs'
      push_cast
      linear_combination -h0 / 2
    have h4 : ((1 : ℂ) - 2 * s) ^ 2 = 4 * (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 := by push_cast; ring
    have hs2 : (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ hs'
    have hPP : polarPart 1 a ((1 / 2 : ℝ) : ℂ) s = (c : ℂ) / 4 / (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 := by
      unfold polarPart
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp [hadef]
    rw [hPP]
    simp only [hgdef]
    rw [h4]
    field_simp
    ring
  have hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder 0 (fun _ => 1) x.1 x.2 (1 / 2) ≤ 1 + 1 :=
    fun x _ => poleOrder_le _ _ x.1 x.2 _
  have := chartPolarCoeff_eq_of_eventuallyEq p hF 0 (fun _ => 1) hp0 hμ hD hev ha
  exact ⟨by simpa [hadef] using this 1 le_rfl, by simpa [hadef] using this 0 zero_le_one⟩

/-- The canonical depth of the `x²y²` chart at cutoff `1` is `(2, 2)`. -/
theorem depthOf_xy_sq : depthOf (0 : Fin 2 → ℕ) (fun _ => 1) 1 = fun _ => 2 := by
  funext i; simp [depthOf]

theorem flatStrip_xy_sq_half :
    FlatStrip (fun _ => 2 : Fin 2 → ℕ) 0 (fun _ => 1) ((1 / 2 : ℝ) : ℂ) := fun _ => by
  simp

/-- The coupling kernel at `½` against a real function is the real fluctuation-type integral. -/
theorem integral_coupKernel_half_mul_ofReal (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), coupKernel ((1 / 2 : ℝ) : ℂ) t * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-t) * f t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  unfold coupKernel
  rw [show ((1 / 2 : ℝ) : ℂ) - 1 = (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht'.le]
  push_cast
  ring

/-- ★★ **The coupling-average coefficients of the `x²y²` chart with constant field `a`.** -/
theorem couplingPolarCoeff_xy_sq (a : ℝ) :
    couplingPolarCoeff (fun _ : Fin 2 => 2) (fun _ => 1) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 =
        (fluctuation 1 (1 / 2) a / 4 : ℝ) ∧
      couplingPolarCoeff (fun _ : Fin 2 => 2) (fun _ => 1) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0 =
        (deriv (fun ν => fluctuation 1 ν a) (1 / 2) / 4 : ℝ) := by
  have hp0 : ∀ i : Fin 2, 0 < (fun _ => 2 : Fin 2 → ℕ) i := fun _ => two_pos
  -- the tilted amplitudes are constant
  have hcoef : ∀ t : ℝ,
      chartPolarCoeff (fun _ => 2) (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) 0
          (fun _ => 1) (1 / 2) 1 = (Real.exp (Real.sqrt t * a) : ℂ) / 4 ∧
      chartPolarCoeff (fun _ => 2) (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) 0
          (fun _ => 1) (1 / 2) 0 = 0 := fun t =>
    chartPolarCoeff_const_xy_sq _ hp0 flatStrip_xy_sq_half
      (c := Real.exp (Real.sqrt t * a)) fun v => by simp [fieldFam]
  constructor
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton]
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, mul_one]
    simp_rw [(hcoef _).1]
    have hfun : (fun t : ℝ => coupKernel ((1 / 2 : ℝ) : ℂ) t *
        ((Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => coupKernel ((1 / 2 : ℝ) : ℂ) t * ((Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) := by
      funext t; push_cast; ring
    rw [hfun, integral_coupKernel_half_mul_ofReal]
    congr 1
    unfold fluctuation
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show Real.exp (-1 * t + 1 * a * Real.sqrt t) = Real.exp (-t) * Real.exp (Real.sqrt t * a) by
      rw [← Real.exp_add]; ring_nf]
    ring
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 0 2 = {0, 1} from rfl, Finset.sum_pair (by norm_num)]
    simp only [Nat.sub_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
      pow_zero, pow_one, mul_one]
    simp_rw [(hcoef _).1, (hcoef _).2]
    simp only [mul_zero, integral_zero, zero_add]
    have hfun : (fun t : ℝ => coupKernel ((1 / 2 : ℝ) : ℂ) t * (Real.log t : ℂ) *
        ((Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => coupKernel ((1 / 2 : ℝ) : ℂ) t *
          ((Real.log t * Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) := by
      funext t; push_cast; ring
    rw [hfun, integral_coupKernel_half_mul_ofReal, ← iteratedDeriv_one,
      iteratedDeriv_fluctuation_eq (by norm_num) a 1]
    congr 1
    unfold fluctuationLog
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show Real.exp (-t + a * Real.sqrt t) = Real.exp (-t) * Real.exp (Real.sqrt t * a) by
      rw [← Real.exp_add]; ring_nf]
    ring

/-- ★★★ **Regression**: the empirical coefficients of the `x²y²` chart with constant field `a`
at `μ = ½` — via the coupling-average formula — are `S_{½}(a)/4` and `−∂_ν S_ν(a)|_{½}/4`. -/
theorem empCoeff_xy_sq_one (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 =
      fluctuation 1 (1 / 2) a / 4 := by
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  have hL : L₀ (0 : Fin 2 → ℕ) ≤ 1 := by simp [L₀]
  have hQ : Qamb (fun _ => 1 : Fin 2 → ℕ) = 2 := by simp [Qamb]
  have hlat : (1 / 2 : ℝ) ∈ latticeBelow (Qamb (fun _ => 1 : Fin 2 → ℕ)) ((1 : ℕ) : ℝ) := by
    rw [hQ]
    have := mem_latticeBelow (Q := 2) two_pos (L := ((1 : ℕ) : ℝ)) (m := 1) (by norm_num)
    simpa using this
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const hk hL hlat
    (by norm_num) (by norm_num) (q := 1) (by norm_num)
  rw [depthOf_xy_sq, (couplingPolarCoeff_xy_sq a).1] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem empCoeff_xy_sq_zero (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0 =
      -(deriv (fun ν => fluctuation 1 ν a) (1 / 2)) / 4 := by
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  have hL : L₀ (0 : Fin 2 → ℕ) ≤ 1 := by simp [L₀]
  have hQ : Qamb (fun _ => 1 : Fin 2 → ℕ) = 2 := by simp [Qamb]
  have hlat : (1 / 2 : ℝ) ∈ latticeBelow (Qamb (fun _ => 1 : Fin 2 → ℕ)) ((1 : ℕ) : ℝ) := by
    rw [hQ]
    have := mem_latticeBelow (Q := 2) two_pos (L := ((1 : ℕ) : ℝ)) (m := 1) (by norm_num)
    simpa using this
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const hk hL hlat
    (by norm_num) (by norm_num) (q := 0) (by norm_num)
  rw [depthOf_xy_sq, (couplingPolarCoeff_xy_sq a).2] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- ★ **Consistency with the direct asymptotic** `tendsto_logExample`: the leading behaviour of
`∫∫ e^{−n x²y² + a√n xy}` is `n^{−½}(log n · c_{½,1} + c_{½,0})` with the coefficients of
`empCoeff_xy_sq_one`/`empCoeff_xy_sq_zero`. -/
theorem tendsto_logExample_empCoeff (a : ℝ) :
    Tendsto (fun n : ℝ => Real.sqrt n * logExample a n -
      (Real.log n * empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 +
        empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0)) atTop
          (𝓝 0) := by
  rw [empCoeff_xy_sq_one, empCoeff_xy_sq_zero]
  have := (tendsto_logExample a).const_mul (1 / 4 : ℝ)
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  ring

end Example

end Grammar
```

## Grammar/ResolvedLeadingMeasure.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalResolvedLeading
import Grammar.LeadingFaceMeasure

/-!
# The leading measures on the resolved space (polar-distribution plan, unit 19)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The library's face measures on `U`
(`faceMeasureU Y p J μ`, the pushforward of the face density `faceNorm' · ρf · residueWeight` along
the face map, and its tilted version `empFaceMeasureU Y p J ξ μ` with the fluctuation density of
the branch trace) were used through their restrictions to the OPEN stratum `X = U ∖ D_{m+1}` and
against test functions.  At the leading pair `(λ, m)` of a chart-leading transport the
complementary walls of every attaining face carry exponents `> λ`, so the face densities are
integrable against every BOUNDED observable (`integrable_faceDensity_mul_leading`), and the sums

  `leadingResidueMeasureU λ m   = Σ_p Σ_{J ∈ simpleFaces p λ m} faceMeasureU Y p J λ`
  `empiricalLeadingMeasureU ξ λ m = Γ(λ)/(m−1)! · Σ_p Σ_{J ∈ simpleFaces p λ m}
empFaceMeasureU Y p J ξ λ`

are FINITE measures on `U` (`isFiniteMeasure_leadingResidueMeasureU`,
`isFiniteMeasure_empiricalLeadingMeasureU`).  The leading term of the empirical partition function
is then the integral of the observable against the tilted leading measure for EVERY observable
(★★★ `hasLeadingTerm_empZ_eq_integral_leadingU`, no test hypothesis: the identification
`integral_pieceFaceLimit_eq_faceRef` of the piece face limits with the face integrals uses only the
boundedness of the observable on the compact face), and at the zero field the population partition
function has the leading term `residueConst λ m · ∫ F dρ` against the raw measure
(★★ `hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU`).  The raw measure is the
`(m−1)!/Γ(λ)`-multiple of the population coefficient measure (Astra #169: keep the two
normalisations distinct).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### Unconditional integral formulas for the face measures on `U` -/

section Integrals

variable (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))

/-- Integrals against the face measure on `U` are density integrals on the face. -/
theorem integral_faceMeasureU (μ : ℝ) {G : Ξ.R.U → ℝ} (hG : Measurable G) :
    ∫ x, G x ∂(Ξ.faceMeasureU Y p J μ) =
      ∫ z, Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold faceMeasureU
  rw [integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hG.aestronglyMeasurable]
  have hmeas : Measurable fun z => (Ξ.faceDensity Y p J μ z).toNNReal :=
    (Ξ.measurable_faceDensity Y p J μ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.faceDensity Y p J μ z)) =
      fun z => ((Ξ.faceDensity Y p J μ z).toNNReal : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Ξ.faceDensity_nonneg Y p J μ hz)]

/-- Integrals against the tilted face measure on `U`. -/
theorem integral_empFaceMeasureU (ξ : Ξ.RootField Y) {μ : ℝ} (hμ : 0 < μ) {G : Ξ.R.U → ℝ}
    (hG : Measurable G) :
    ∫ x, G x ∂(Ξ.empFaceMeasureU Y p J ξ μ) =
      ∫ z, Ξ.empFaceDensity Y p J ξ μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold empFaceMeasureU
  rw [integral_map (Ξ.measurable_faceMap Y p J).aemeasurable hG.aestronglyMeasurable]
  have hmeas : Measurable fun z => (Ξ.empFaceDensity Y p J ξ μ z).toNNReal :=
    (Ξ.measurable_empFaceDensity Y p J ξ hμ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p J ξ μ z)) =
      fun z => ((Ξ.empFaceDensity Y p J ξ μ z).toNNReal : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  simp only [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Ξ.empFaceDensity_nonneg Y p J ξ hμ hz)]

/-- An observable smooth on `U` is bounded on the face of a piece. -/
theorem exists_bound_faceMap {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∃ C : ℝ, ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) → |G (Ξ.faceMap Y p J z)| ≤ C := by
  have hcont : ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      G ((Y.φ p.1).symm ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))))
      ((univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
        (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1))) := by
    refine hG.continuous.comp_continuousOn ((Y.φ p.1).continuousOn_symm.comp
      (((Ξ.X Y).continuous_Tm p).comp
        (continuous_fst.prodMk ((continuous_glue_zero J).comp continuous_snd))).continuousOn
      fun z hz => ?_)
    exact Ξ.facePt_mem_target Y p z.1
      (glue_zero_mem_closedBox_of_mem_Icc (Y.T.a_pos p.1).le fun i _ => hz.2 i (mem_univ i))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod
    (isCompact_univ_pi fun _ => isCompact_Icc)).exists_bound_of_continuousOn hcont
  refine ⟨C, fun z hz => ?_⟩
  rw [Ξ.faceMap_eq_divPt Y p J hz]
  have hz' : z ∈ (univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
      (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1)) :=
    ⟨mem_univ _, fun i _ => Ioc_subset_Icc_self (hz i (mem_univ i))⟩
  simpa [divPt, facePt, Real.norm_eq_abs] using hC z hz'

end Integrals

/-! ### Integrability at the leading face -/

section Leading

variable (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}

/-- The face density of the leading face is integrable against every observable bounded on the
face: the complementary walls carry exponents `> λ`. -/
theorem integrable_faceDensity_mul_leading (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    {G : Ξ.R.U → ℝ} (hGm : Measurable G) {C : ℝ}
    (hGC : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
      ({i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} → ℝ),
      z.2 ∈ box _ (Y.T.a p.1) → |G (Ξ.faceMap Y p _ z)| ≤ C) :
    Integrable (fun z => Ξ.faceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) lam z *
      G (Ξ.faceMap Y p _ z)) (Ξ.faceRef Y p _) := by
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  -- a uniform bound on the transport density on the closed face
  have hcont : ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2)))
      ((univ : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))) ×ˢ
        (Set.univ.pi fun _ : {i // ¬ inJ J i} => Icc (0 : ℝ) (Y.T.a p.1))) :=
    (((Ξ.X Y).contDiff_ρf p.1).continuous.comp (((Ξ.X Y).continuous_Tm p).comp
      (continuous_fst.prodMk ((continuous_glue_zero J).comp continuous_snd)))).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_univ.prod
    (isCompact_univ_pi fun _ => isCompact_Icc)).exists_bound_of_continuousOn hcont
  have hM' : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
      |(Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))| ≤ M := fun z hz => by
    have := hM z ⟨mem_univ _, fun i _ => Ioc_subset_Icc_self (hz i (mem_univ i))⟩
    simpa [Real.norm_eq_abs] using this
  have hN0 : 0 ≤ Ξ.faceNorm' Y p J := (Ξ.faceNorm'_pos Y p J).le
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  -- the integrable majorant `faceNorm' · M · C · residueWeight`
  have hmaj : Integrable (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.faceNorm' Y p J * max M 0 * max C 0) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2) (Ξ.faceRef Y p J) := by
    unfold faceRef
    exact (integrable_const (μ := (Ξ.piecePresentation Y p).ν) _).mul_prod
      (integrableOn_residueWeight_compl (h := (Ξ.X Y).hA p) (k := (Ξ.X Y).kA p) (l := lam)
        ((Ξ.X Y).kA_pos p) hlead.1 (Y.T.a_pos p.1).le)
  refine hmaj.mono' ((Ξ.measurable_faceDensity Y p J lam).mul
    (hGm.comp (Ξ.measurable_faceMap Y p J))).aestronglyMeasurable ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  unfold faceDensity
  have hrw : 0 ≤ residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i)
      (fun i => (Ξ.X Y).kA p i) lam z.2 := residueWeight_nonneg _ _ lam hz
  rw [abs_mul, abs_mul, abs_of_nonneg hN0, abs_of_nonneg hrw]
  calc Ξ.faceNorm' Y p J * |(Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))| *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2 *
        |G (Ξ.faceMap Y p J z)|
      ≤ Ξ.faceNorm' Y p J * max M 0 *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i)
          lam z.2 *
        max C 0 := by
        gcongr
        · exact (hM' z hz).trans (le_max_left _ _)
        · exact (hGC z hz).trans (le_max_left _ _)
    _ = _ := by ring

/-- The tilted face density of the leading face is integrable against every bounded observable. -/
theorem integrable_empFaceDensity_mul_leading (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {G : Ξ.R.U → ℝ} (hGm : Measurable G)
    {C : ℝ}
    (hGC : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
      ({i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} → ℝ),
      z.2 ∈ box _ (Y.T.a p.1) → |G (Ξ.faceMap Y p _ z)| ≤ C) :
    Integrable (fun z => Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ lam z *
      G (Ξ.faceMap Y p _ z)) (Ξ.faceRef Y p _) := by
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  obtain ⟨M, -, hM⟩ := ξ.exists_bound
  have hint := Ξ.integrable_faceDensity_mul_leading Y p hlead hGm hGC
  have h := hint.bdd_mul (c := fluctDensity lam M)
    ((continuous_fluctDensity hμ).comp (Ξ.continuous_faceTrace Y p J ξ)).aestronglyMeasurable
    (by
      filter_upwards [Ξ.ae_faceRef_mem_box Y p J] with z hz
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (fluctDensity_pos hμ _)]
      exact fluctDensity_le_of_abs_le hμ (Ξ.faceTrace_abs_le Y p J ξ (hM p) hz))
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, empFaceDensity]
  ring

/-- ★ **Identification of the piece face limit without a test hypothesis**: for an attaining
piece, `∫_{Base} pieceFaceLimit dν_p = residueConst λ m · ∫ empFaceDensity · F ∘ faceMap
  d(faceRef)`. -/
theorem integral_pieceFaceLimit_eq_faceRef (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    (hmc : multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m) :
    ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν =
      residueConst lam m * ∫ z, Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ
        lam z * Ξ.F (Ξ.faceMap Y p _ z) ∂(Ξ.faceRef Y p _) := by
  obtain ⟨C, hC⟩ := Ξ.exists_bound_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)
    Ξ.F_smooth
  rw [← integral_const_mul]
  unfold faceRef
  rw [integral_prod _ ((Ξ.integrable_empFaceDensity_mul_leading Y p ξ hμ hlead
    Ξ.F_smooth.continuous.measurable hC).const_mul (residueConst lam m))]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [pieceFaceLimit, boxFaceLimit, if_pos hmc, faceFunctional]
  rw [← integral_const_mul]
  set J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam with hJ
  refine setIntegral_congr_fun (measurableSet_box _) fun w hw => ?_
  have hface := Ξ.faceDensity_mul_eq Y p J Ξ.F_smooth lam (z := (s, w)) hw
  have hamp : (Ξ.ampObs Y p Ξ.F_smooth).amp s (glue J 0 w) =
    (Ξ.amp Y p).amp s (glue J 0 w) := rfl
  rw [hamp] at hface
  unfold empFaceDensity
  rw [show Ξ.faceDensity Y p J lam (s, w) * fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
      Ξ.F (Ξ.faceMap Y p J (s, w)) =
      fluctDensity lam (Ξ.faceTrace Y p J ξ (s, w)) *
        (Ξ.faceDensity Y p J lam (s, w) * Ξ.F (Ξ.faceMap Y p J (s, w))) by ring, hface,
    Ξ.faceNorm'_eq_inv_prod Y p J]
  unfold faceTrace fluctDensity residueConst
  dsimp only
  rw [hmc]
  have hΓ : Real.Gamma lam ≠ 0 := (Real.Gamma_pos_of_pos hμ).ne'
  have hfact : ((m - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hprod : (∏ i ∈ J, (2 * ((Ξ.X Y).kA p i : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      have := Nat.cast_pos (α := ℝ) |>.2 ((Ξ.X Y).kA_pos p i)
      positivity
  field_simp

end Leading

/-! ### The leading measures on `U` -/

section Assembly

variable {lam : ℝ} {m : ℕ}

/-- ★★ **The raw leading measure** on `U` at `(λ, m)`: the sum over the pieces and their simple
faces of size `m` of the face measures. -/
noncomputable def leadingResidueMeasureU (lam : ℝ) (m : ℕ) : Measure Ξ.R.U :=
  ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m, Ξ.faceMeasureU Y p J lam

/-- ★★ **The tilted leading measure** on `U` at `(λ, m)` for the root field `ξ`, with the
coefficient normalisation `Γ(λ)/(m−1)!`. -/
noncomputable def empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ) :
    Measure Ξ.R.U :=
  ENNReal.ofReal (residueConst lam m) •
    ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m, Ξ.empFaceMeasureU Y p J ξ lam

/-- Every simple face of size `m` of a chart-leading piece is the resonant set. -/
theorem eq_resSet_of_mem_simpleFaces (p : (Ξ.X Y).PIdx)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {J : Finset (Fin ((Ξ.X Y).da p))}
    (hJ : J ∈ Ξ.simpleFaces Y p lam m) :
    J = resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam ∧
      multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m := by
  rcases lt_or_eq_of_le hlead.2 with hlt | heq
  · rw [Ξ.simpleFaces_eq_empty Y p hlt] at hJ
    exact absurd hJ (Finset.notMem_empty _)
  · rw [Ξ.simpleFaces_eq_singleton Y p heq, Finset.mem_singleton] at hJ
    exact ⟨hJ, heq⟩

/-- Integrability of a bounded observable against a tilted face measure of a chart-leading
piece. -/
theorem integrable_empFaceMeasureU_of_bounded (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (p : (Ξ.X Y).PIdx) (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m)
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J ∈ Ξ.simpleFaces Y p lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Integrable G (Ξ.empFaceMeasureU Y p J ξ lam) := by
  obtain ⟨rfl, -⟩ := Ξ.eq_resSet_of_mem_simpleFaces Y p hlead hJ
  obtain ⟨C, hC⟩ := Ξ.exists_bound_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) hG
  unfold empFaceMeasureU
  rw [integrable_map_measure hG.continuous.measurable.aestronglyMeasurable
    (Ξ.measurable_faceMap Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)).aemeasurable]
  have hmeas : Measurable fun z => (Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
    lam) ξ lam z).toNNReal :=
    (Ξ.measurable_empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ hμ).real_toNNReal
  have hd : (fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA
    p) lam) ξ lam z)) =
      fun z => ((Ξ.empFaceDensity Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) ξ lam
        z).toNNReal : ENNReal) := rfl
  rw [hd, integrable_withDensity_iff_integrable_smul hmeas]
  refine (Ξ.integrable_empFaceDensity_mul_leading Y p ξ hμ hlead hG.continuous.measurable
    hC).congr ?_
  filter_upwards [Ξ.ae_faceRef_mem_box Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)] with z hz
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Ξ.empFaceDensity_nonneg Y p (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)
      lam) ξ hμ hz)]

theorem integrable_faceMeasureU_of_bounded (hμ : 0 < lam) (p : (Ξ.X Y).PIdx)
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) {J : Finset (Fin ((Ξ.X Y).da p))}
    (hJ : J ∈ Ξ.simpleFaces Y p lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Integrable G (Ξ.faceMeasureU Y p J lam) := by
  have := Ξ.integrable_empFaceMeasureU_of_bounded Y (RootField.zero Ξ Y) hμ p hlead hJ hG
  rwa [Ξ.empFaceMeasureU_zero Y p J hμ] at this

/-- ★ Integrals of smooth observables against the tilted leading measure. -/
theorem integral_empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∫ x, G x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m) =
      residueConst lam m * ∑ p : (Ξ.X Y).PIdx, ∑ J ∈ Ξ.simpleFaces Y p lam m,
        ∫ z, Ξ.empFaceDensity Y p J ξ lam z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) := by
  unfold empiricalLeadingMeasureU
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    integral_finsetSum_measure fun p _ => integrable_finsetSum_measure.2 fun J hJ =>
      Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ hG]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum_measure fun J hJ =>
    Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ hG]
  exact Finset.sum_congr rfl fun J _ =>
    Ξ.integral_empFaceMeasureU Y p J ξ hμ hG.continuous.measurable

/-- At the zero field the tilted leading measure is the coefficient-normalised raw measure. -/
theorem empiricalLeadingMeasureU_zero (hμ : 0 < lam) (m : ℕ) :
    Ξ.empiricalLeadingMeasureU Y (RootField.zero Ξ Y) lam m =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m := by
  unfold empiricalLeadingMeasureU leadingResidueMeasureU
  refine congrArg (fun ν : Measure Ξ.R.U => ENNReal.ofReal (residueConst lam m) • ν)
    (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun J _ => ?_)
  exact Ξ.empFaceMeasureU_zero Y p J hμ

/-- ★★★ **The empirical leading theorem for every observable**: at a chart-leading pair and for
a bounded root field, `N^λ (log N)^{−(m−1)} Z^{emp}_N[F; ξ] → ∫_U F dν̂^λ_m(ξ)` against the tilted
leading measure on `U` — no test hypothesis on `F`. -/
theorem hasLeadingTerm_empZ_eq_integral_leadingU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m)) lam
      (m - 1) := by
  have hsum : ∀ p : (Ξ.X Y).PIdx, residueConst lam m * ∑ J ∈ Ξ.simpleFaces Y p lam m,
      ∫ z, Ξ.empFaceDensity Y p J ξ lam z * Ξ.F (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J) =
      ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
    intro p
    rcases lt_or_eq_of_le (hlead p).2 with hlt | heq
    · rw [Ξ.simpleFaces_eq_empty Y p hlt, Finset.sum_empty, mul_zero]
      symm
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [pieceFaceLimit, boxFaceLimit, if_neg hlt.ne, Pi.zero_apply]
    · rw [Ξ.simpleFaces_eq_singleton Y p heq, Finset.sum_singleton,
        Ξ.integral_pieceFaceLimit_eq_faceRef Y p ξ hμ (hlead p) heq]
  have htot : ∫ x, Ξ.F x ∂(Ξ.empiricalLeadingMeasureU Y ξ lam m) =
      ∑ p : (Ξ.X Y).PIdx, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν := by
    rw [Ξ.integral_empiricalLeadingMeasureU Y ξ hμ hlead Ξ.F_smooth, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => hsum p
  rw [htot]
  exact Ξ.hasLeadingTerm_empZ Y ξ hm hlead hM

/-- ★★ **The population leading theorem for every observable**: at a chart-leading pair,
`N^λ (log N)^{−(m−1)} Z_N[F] → residueConst λ m · ∫_U F dρ^λ_m` against the raw leading
measure. -/
theorem hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU (hμ : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    HasLeadingTerm Ξ.Z (residueConst lam m * ∫ x, Ξ.F x ∂(Ξ.leadingResidueMeasureU Y lam m)) lam
      (m - 1) := by
  have h := Ξ.hasLeadingTerm_empZ_eq_integral_leadingU Y (RootField.zero Ξ Y) hμ hm hlead
    (M := 0) fun P => by simp [RootField.zero]
  rw [Ξ.empiricalLeadingMeasureU_zero Y hμ m, integral_smul_measure,
    ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  unfold empZ Z empIntegrand
  refine integral_congr_ae (Eventually.of_forall fun P => ?_)
  change Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * 0) * Ξ.F P = _
  rw [mul_zero, add_zero, mul_comm]
  rfl

/-- ★ The tilted leading measure is finite at a chart-leading pair. -/
theorem isFiniteMeasure_empiricalLeadingMeasureU (ξ : Ξ.RootField Y) (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) :
    IsFiniteMeasure (Ξ.empiricalLeadingMeasureU Y ξ lam m) := by
  refine ⟨?_⟩
  unfold empiricalLeadingMeasureU
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun p _ => ?_)
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  have hint := Ξ.integrable_empFaceMeasureU_of_bounded Y ξ hμ p (hlead p) hJ
    (G := fun _ => (1 : ℝ)) contMDiff_const
  exact ((integrable_const_iff.1 hint).resolve_left one_ne_zero).measure_univ_lt_top

theorem isFiniteMeasure_leadingResidueMeasureU (hμ : 0 < lam) (hlead : Ξ.ChartLeading Y lam m) :
    IsFiniteMeasure (Ξ.leadingResidueMeasureU Y lam m) := by
  refine ⟨?_⟩
  unfold leadingResidueMeasureU
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun p _ => ?_
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J hJ => ?_
  have hint := Ξ.integrable_faceMeasureU_of_bounded Y hμ p (hlead p) hJ (G := fun _ => (1 : ℝ))
    contMDiff_const
  exact ((integrable_const_iff.1 hint).resolve_left one_ne_zero).measure_univ_lt_top

end Assembly

end ResolvedData

end SmoothEngine

end Grammar
```

## Grammar/ResolvedExtremalLocalisation.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolvedLeadingMeasure
import Grammar.SmoothStratumMeasureExtremal

/-!
# Extremal localisation of the leading measure (polar-distribution plan, unit 20)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The population leading theorem of unit 19
(`hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU`) is stated at a CHART-leading pair: every
piece box of the transport has all wall ratios `≥ λ` and at most `m` walls of ratio `λ`.  The
intrinsic notion is the EXTREMAL data `(λ*, m*)` of the zero fibre (`IsExtremalData`): every wall
through a point of `Z₀` has ratio `≥ λ*` and at most `m*` walls through any point of `Z₀` resonate
with `λ*`.  The two differ exactly on the pieces whose walls do not all pass through a point of the
zero fibre, so the bridge is a CERTIFICATE (`ExtremalCertificate`): every piece's wall multiset
`pieceWalls p = {(k_i, h_i)}` sits inside the intrinsic pair data of some point of the zero fibre.
The certificate holds whenever the chart centres lie in the zero fibre
(`extremalCertificate_of_divPt_zero`, via `pairs_divPt_zero`), and

  `IsExtremalData λ m ∧ ExtremalCertificate ⟹ ChartLeading λ m`

(★★ `chartLeading_of_extremalData`: the ratio bound is clause 1 of the extremal data and the
multiplicity count is bounded by the resonance count of clause 2, since a wall of ratio exactly `λ`
resonates with `λ`).

With the bridge `hasLeadingTerm_iff_tendsto_normalised` between the two normalisation conventions
of the library, uniqueness of limits identifies the population coefficient functional at the
extremal pair with the raw leading measure for EVERY smooth observable, with no test hypothesis:

  `𝒯^U_{λ*,m*−1}[G] = Γ(λ*)/(m*−1)! · ∫_U G dρ^{λ*}_{m*}`

(★★★ `coeff_withF_eq_integral_leadingResidueMeasureU`).  Downstairs this gives the leading
asymptotic of `∫ prior · f · e^{−NK}` for every smooth `f` against the pull-back of the raw
measure (★★★ `tendsto_normalised_partitionObs_extremal_all`,
`partitionObs_isEquivalent_extremal_all`), and the leading coefficient of the partition function
is the total mass `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)` (`coeff_one_eq_mass_leadingResidueMeasureU`).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### The two normalisation conventions -/

/-- `Z(N)/(N^{−λ} (log N)^k) → c` iff `N^λ (log N)^{−k} Z(N) → c`. -/
theorem hasLeadingTerm_iff_tendsto_normalised {Z : ℝ → ℝ} {c lam : ℝ} {k : ℕ} :
    HasLeadingTerm Z c lam k ↔ Tendsto (normalised lam k Z) atTop (𝓝 c) := by
  unfold HasLeadingTerm
  refine tendsto_congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  unfold normalised powLogScale
  rw [Real.rpow_neg hN.le, div_eq_mul_inv, mul_inv, inv_inv, div_eq_mul_inv]
  ring

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The wall multiset of a piece and the certificate -/

/-- The wall multiset `{(k_i, h_i) : i}` of a piece of the transport. -/
noncomputable def pieceWalls (p : (Ξ.X Y).PIdx) : Multiset (ℕ × ℕ) :=
  (Finset.univ : Finset (Fin ((Ξ.X Y).da p))).val.map fun i => ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i)

/-- The intrinsic pair data of the divisor point at the origin of the box is the wall multiset of
the piece. -/
theorem pairs_divPt_zero (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    pairs Ξ.R Ξ.hK0 (Ξ.divPt Y p s 0) = Ξ.pieceWalls Y p := by
  have h0 : (0 : Fin ((Ξ.X Y).da p) → ℝ) ∈ closedBox _ (Y.T.a p.1) :=
    mem_closedBox.2 fun i => ⟨le_rfl, (Y.T.a_pos p.1).le⟩
  rw [pairs_eq_of_mem_source Ξ.R Ξ.hK0 (Y.evenChartBox p.1) (Ξ.divPt_mem_source Y p s h0),
    Y.evenChartBox_φ, Ξ.φ_divPt Y p s h0,
    Ξ.wallsAt_facePt_eq Y p s (J := Finset.univ) (fun i => by simp), Finset.map_val,
    Multiset.map_map]
  rfl

/-- **The extremal certificate**: the wall multiset of every piece sits inside the intrinsic pair
data of some point of the zero fibre. -/
def ExtremalCertificate : Prop :=
  ∀ p : (Ξ.X Y).PIdx, ∃ P ∈ Ξ.zeroFibre, Ξ.pieceWalls Y p ≤ pairs Ξ.R Ξ.hK0 P

/-- The certificate holds when every piece has a box origin in the zero fibre. -/
theorem extremalCertificate_of_divPt_zero
    (h : ∀ p : (Ξ.X Y).PIdx, ∃ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      Ξ.divPt Y p s 0 ∈ Ξ.zeroFibre) :
    Ξ.ExtremalCertificate Y := fun p => by
  obtain ⟨s, hs⟩ := h p
  exact ⟨_, hs, (Ξ.pairs_divPt_zero Y p s).symm ▸ le_rfl⟩

/-- A wall of ratio exactly `λ` resonates with `λ`. -/
theorem resonates_of_ratioExp_eq {h k : Fin d → ℕ} {lam : ℝ} {i : Fin d} (hk : 0 < k i)
    (hi : ratioExp h k i = lam) : Resonates lam (k i, h i) := by
  refine ⟨0, ?_⟩
  unfold ratioExp at hi
  have hk' : (0 : ℝ) < k i := by exact_mod_cast hk
  rw [← hi]
  push_cast
  field_simp
  ring

open Classical in
/-- ★★ **Extremal data plus the certificate give the chart-leading condition**. -/
theorem chartLeading_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) : Ξ.ChartLeading Y lam m := by
  intro p
  obtain ⟨P, hP, hle⟩ := hc p
  have hmem : ∀ i, ((Ξ.X Y).kA p i, (Ξ.X Y).hA p i) ∈ pairs Ξ.R Ξ.hK0 P := fun i =>
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩)
  refine ⟨fun i => ?_, ?_⟩
  · have hi := h.1 P hP _ (hmem i)
    have hk : (0 : ℝ) < (Ξ.X Y).kA p i := by exact_mod_cast (Ξ.X Y).kA_pos p i
    unfold ratioExp
    rw [le_div_iff₀ (by positivity)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi
  · calc multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam
        = ((Finset.univ.filter fun i =>
            ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) i = lam).val).card := by
          rw [multCount, ← Finset.card_filter, Finset.card_def]
      _ ≤ ((Ξ.pieceWalls Y p).filter (Resonates lam)).card := by
          unfold pieceWalls
          rw [Multiset.filter_map, Multiset.card_map, Finset.filter_val]
          exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun i hi =>
            resonates_of_ratioExp_eq ((Ξ.X Y).kA_pos p i) hi)
      _ ≤ ((pairs Ξ.R Ξ.hK0 P).filter (Resonates lam)).card :=
          Multiset.card_le_card (Multiset.filter_le_filter _ hle)
      _ = resonanceCount Ξ.R Ξ.hK0 lam P := rfl
      _ ≤ m := h.2 P hP

/-! ### The population coefficient functional at the extremal pair -/

/-- ★★★ **The extremal coefficient functional is the raw leading measure** for every smooth
observable: `𝒯^U_{λ*,m*−1}[G] = Γ(λ*)/(m*−1)! · ∫_U G dρ^{λ*}_{m*}`. -/
theorem coeff_withF_eq_integral_leadingResidueMeasureU {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).coeff Y lam (m - 1) =
      residueConst lam m * ∫ x, G x ∂(Ξ.leadingResidueMeasureU Y lam m) :=
  tendsto_nhds_unique (Ξ.tendsto_normalised_Z_of_extremalData Y h hG)
    (hasLeadingTerm_iff_tendsto_normalised.1
      ((Ξ.withF G hG).hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU Y hμ hm
        (Ξ.chartLeading_of_extremalData Y h hc)))

/-- The leading coefficient of the partition function is the total mass
`Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)` of the raw leading measure. -/
theorem coeff_one_eq_mass_leadingResidueMeasureU {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) =
      residueConst lam m * (Ξ.leadingResidueMeasureU Y lam m).real univ := by
  rw [Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm contMDiff_const,
    integral_const, smul_eq_mul, mul_one]

/-! ### Downstairs: every smooth observable -/

/-- ★★★ **The leading asymptotic downstairs for every smooth observable**:
`N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → Γ(λ*)/(m*−1)! · ∫_U f ∘ π dρ^{λ*}_{m*}`. -/
theorem tendsto_normalised_partitionObs_extremal_all {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (residueConst lam m *
        ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m))) := by
  have key := Ξ.tendsto_normalised_Z_of_extremalData Y h (Ξ.contMDiff_comp_gv hf)
  rw [Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm] at key
  refine key.congr fun N => ?_
  unfold normalised
  rw [Ξ.Z_withF_comp_gv hf N]

/-- ★★★ **The leading asymptotic with insertion, for every smooth observable**: when
`∫ f ∘ π dρ^{λ*}_{m*} ≠ 0`,
`∫ prior · f · e^{−NK} ∼ Γ(λ*)/(m*−1)! (∫ f ∘ π dρ^{λ*}_{m*}) N^{−λ*} (log N)^{m*−1}`. -/
theorem partitionObs_isEquivalent_extremal_all {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y)
    (hμ : 0 < lam) (hm : 1 ≤ m)
    (hne : ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m) ≠ 0) :
    (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
      fun N => (residueConst lam m * ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m)) *
        (N ^ (-lam) * Real.log N ^ (m - 1)) := by
  set I := residueConst lam m * ∫ x, f (Ξ.R.gv x) ∂(Ξ.leadingResidueMeasureU Y lam m) with hI
  have hIne : I ≠ 0 := mul_ne_zero (residueConst_pos hμ m).ne' hne
  have hv : ∀ᶠ N : ℝ in atTop, I * (N ^ (-lam) * Real.log N ^ (m - 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    exact mul_ne_zero hIne (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hN) _)).ne'
  refine (Asymptotics.isEquivalent_iff_tendsto_one hv).2 ?_
  have hlim := (Ξ.tendsto_normalised_partitionObs_extremal_all Y hf h hc hμ hm).div_const I
  rw [div_self hIne] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN0 : 0 ≤ N := by linarith
  have hA : (N ^ lam : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log N ^ (m - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hN) _).ne'
  simp only [Pi.div_apply]
  unfold normalised
  rw [Real.rpow_neg hN0]
  field_simp

end ResolvedData

end SmoothEngine

end Grammar
```

## Grammar/SmoothGlobalLeadingMeasure.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolvedExtremalLocalisation

/-!
# The global leading measure and the extremal stratum measure (polar-distribution plan, unit 21)

Consult #169 (`tide-log/gpt6_leading_v169.md`).  The extremal stratum measure `ν^{λ*}_{m*}` of the
library lives on the open stratum `X = U ∖ D_{m*+1}` and is characterised by its integrals of the
smooth TEST functions (compactly supported in `X`); the raw leading measure `ρ^{λ*}_{m*}` of unit 19
lives on all of `U` and represents the coefficient functional on EVERY smooth observable (unit 20).
On the tests the two representations agree, so by the uniqueness theorem
`eq_stratumMeasure_of_tests` (regularity of the restriction of a finite measure to an open subset
of the σ-compact metrisable manifold `U`):

  `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`  (★★★ `extremalStratumMeasure_eq_leadingResidue`)

Pushing forward along `X ↪ U` gives the GLOBAL extremal stratum measure
`globalExtremalStratumMeasure = Γ(λ*)/(m*−1)! · ρ|_X` on `U`
(★★★ `globalExtremalStratumMeasure_eq_restrict`), and it is the full multiple
`Γ(λ*)/(m*−1)! · ρ` exactly when the raw measure gives the deep fibre `D_{m*+1} ∩ Z₀` measure zero
(★★ `globalExtremalStratumMeasure_eq_iff`).  The deep fibre IS null: a face of `m` walls maps a
point into the deep fibre only when a complementary chart coordinate vanishes, since the intrinsic
depth is the number of vanishing chart coordinates (`depth_divPt_eq`), and the coordinate
hyperplanes are null for the face reference measure (★★ `leadingResidueMeasureU_deepZeroFibre`).
Hence ★★★ `globalExtremalStratumMeasure_eq`: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on all of
`U`, the coefficient functional at the extremal pair is the global stratum measure for EVERY smooth
observable (`coeff_withF_eq_integral_globalExtremalStratumMeasure`), and the extremal stratum
measure is FINITE with total mass `Γ(λ*)/(m*−1)! · ρ(U)` (`extremalStratumMeasure_univ`,
`isFiniteMeasure_extremalStratumMeasure`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The raw leading measure on the open stratum -/

theorem measurableSet_stratumOpen (m : ℕ) : MeasurableSet (Ξ.stratumOpen m) :=
  (Ξ.isOpen_stratumOpen m).measurableSet

theorem measurableSet_deepZeroFibre (m : ℕ) : MeasurableSet (Ξ.deepZeroFibre m) :=
  (Ξ.isCompact_deepZeroFibre m).isClosed.measurableSet

/-- The raw leading measure restricted to the open stratum `X = U ∖ D_{m+1}`. -/
noncomputable def leadingResidueMeasureX (lam : ℝ) (m : ℕ) : Measure (Ξ.stratumOpen m) :=
  (Ξ.leadingResidueMeasureU Y lam m).comap Subtype.val

theorem integral_leadingResidueMeasureX (lam : ℝ) (m : ℕ) (G : Ξ.R.U → ℝ) :
    ∫ x, G x.1 ∂(Ξ.leadingResidueMeasureX Y lam m) =
      ∫ x in Ξ.stratumOpen m, G x ∂(Ξ.leadingResidueMeasureU Y lam m) :=
  integral_subtype_comap (Ξ.measurableSet_stratumOpen m) G

theorem leadingResidueMeasureX_apply (lam : ℝ) (m : ℕ) (s : Set (Ξ.stratumOpen m)) :
    Ξ.leadingResidueMeasureX Y lam m s = Ξ.leadingResidueMeasureU Y lam m (Subtype.val '' s) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).comap_apply _ _

/-- The raw leading measure is regular at a chart-leading pair (finite on the σ-compact
metrisable manifold `U`). -/
theorem regular_leadingResidueMeasureU {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureU Y lam m).Regular :=
  haveI := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem regular_leadingResidueMeasureX {lam : ℝ} {m : ℕ} (hμ : 0 < lam)
    (hlead : Ξ.ChartLeading Y lam m) : (Ξ.leadingResidueMeasureX Y lam m).Regular :=
  haveI := Ξ.regular_leadingResidueMeasureU Y hμ hlead
  Measure.Regular.comap' _ (Ξ.isOpen_stratumOpen m).isOpenEmbedding_subtypeVal

/-! ### The deep fibre is null for the raw leading measure -/

/-- The coordinate hyperplanes of the complementary walls are null for the face reference
measure. -/
theorem faceRef_exists_eq_zero_null (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) :
    Ξ.faceRef Y p J {z | ∃ i, z.2 i = 0} = 0 := by
  have ht : (volume : Measure ({i // ¬ inJ J i} → ℝ)) {w | ∃ i, w i = 0} = 0 := by
    have : {w : {i // ¬ inJ J i} → ℝ | ∃ i, w i = 0} = ⋃ i, {w | w i = 0} := by ext w; simp
    rw [this]
    exact measure_iUnion_null fun i => by rw [volume_pi]; exact Measure.pi_hyperplane _ i 0
  unfold faceRef
  rw [show {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) | ∃ i, z.2 i = 0} =
      univ ×ˢ {w | ∃ i, w i = 0} by ext z; simp, Measure.prod_prod,
    Measure.restrict_apply' (measurableSet_box _), measure_mono_null inter_subset_left ht,
    mul_zero]

/-- A point of the face box mapped into the deep fibre `D_{m+1} ∩ Z₀` by a face of `m` walls has a
vanishing complementary coordinate: the intrinsic depth is the number of vanishing chart
coordinates (`depth_divPt_eq`). -/
theorem exists_eq_zero_of_faceMap_mem_deepZeroFibre (p : (Ξ.X Y).PIdx) {m : ℕ}
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J.card = m)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) (hmem : Ξ.faceMap Y p J z ∈ Ξ.deepZeroFibre m) :
    ∃ i, z.2 i = 0 := by
  by_contra hne
  simp only [not_exists] at hne
  have hdepth : m + 1 ≤ depth Ξ.R Ξ.hK0 (Ξ.faceMap Y p J z) := hmem.2
  rw [Ξ.faceMap_eq_divPt Y p J hz, Ξ.depth_divPt_eq Y p z.1
    (Ξ.glue_mem_closedBox_of_mem_box Y p J hz) (J := J) ?_, hJ] at hdepth
  · omega
  · intro i
    by_cases hi : i ∈ J
    · simp [glue_apply_of_mem J _ _ hi, hi]
    · simp [glue_apply_of_not_mem J _ _ hi, hi, hne ⟨i, hi⟩]

/-- ★ **A face measure of `m` walls gives the deep fibre `D_{m+1} ∩ Z₀` measure zero.** -/
theorem faceMeasureU_deepZeroFibre (p : (Ξ.X Y).PIdx) {m : ℕ}
    {J : Finset (Fin ((Ξ.X Y).da p))} (hJ : J.card = m) (μ : ℝ) :
    Ξ.faceMeasureU Y p J μ (Ξ.deepZeroFibre m) = 0 := by
  unfold faceMeasureU
  rw [Measure.map_apply (Ξ.measurable_faceMap Y p J) (Ξ.measurableSet_deepZeroFibre m)]
  refine withDensity_absolutelyContinuous _ _ (measure_mono_null (t := {z | z.2 ∉ box
    {i // ¬ inJ J i} (Y.T.a p.1)} ∪ {z | ∃ i, z.2 i = 0}) ?_
    (measure_union_null (ae_iff.1 (Ξ.ae_faceRef_mem_box Y p J))
      (Ξ.faceRef_exists_eq_zero_null Y p J)))
  intro z hz
  by_cases hzb : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)
  · exact Or.inr (Ξ.exists_eq_zero_of_faceMap_mem_deepZeroFibre Y p hJ hzb hz)
  · exact Or.inl hzb

/-- ★★ **Deep-fibre nullity**: the raw leading measure `ρ^λ_m` gives `D_{m+1} ∩ Z₀` measure zero. -/
theorem leadingResidueMeasureU_deepZeroFibre (lam : ℝ) (m : ℕ) :
    Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0 := by
  unfold leadingResidueMeasureU
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun J hJ => ?_
  exact Ξ.faceMeasureU_deepZeroFibre Y p (Finset.mem_filter.1 hJ).2.1 lam

/-- The raw leading measure is carried by the open stratum `X = U ∖ D_{m+1}`. -/
theorem leadingResidueMeasureU_restrict_stratumOpen (lam : ℝ) (m : ℕ) :
    (Ξ.leadingResidueMeasureU Y lam m).restrict (Ξ.stratumOpen m) =
      Ξ.leadingResidueMeasureU Y lam m :=
  Measure.restrict_eq_self_of_ae_mem
    (compl_mem_ae_iff.2 (Ξ.leadingResidueMeasureU_deepZeroFibre Y lam m))

/-! ### The extremal stratum measure is the raw leading measure on the stratum -/

/-- ★★★ **The extremal stratum measure is the raw leading measure on the open stratum**:
`ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_X`. -/
theorem extremalStratumMeasure_eq_leadingResidue {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m := by
  symm
  have := Ξ.regular_leadingResidueMeasureX Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  have : (ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureX Y lam m).Regular :=
    Measure.Regular.smul ENNReal.ofReal_ne_top
  unfold extremalStratumMeasure
  refine Ξ.eq_stratumMeasure_of_tests Y hm _ _ fun G hG hGt => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul,
    Ξ.integral_leadingResidueMeasureX, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => image_eq_zero_of_notMem_tsupport fun hx' => hx (hGt.2 hx')]
  exact (Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm hG).symm

/-- The total mass of the extremal stratum measure is `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}(U)`. -/
theorem extremalStratumMeasure_univ {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ =
      ENNReal.ofReal (residueConst lam m) * Ξ.leadingResidueMeasureU Y lam m univ := by
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.smul_apply, smul_eq_mul,
    Ξ.leadingResidueMeasureX_apply, image_univ, Subtype.range_coe, ← Measure.restrict_apply_univ,
    Ξ.leadingResidueMeasureU_restrict_stratumOpen]

/-- ★ The extremal stratum measure is finite under the certificate. -/
theorem isFiniteMeasure_extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.extremalStratumMeasure Y h hm) := by
  have := Ξ.isFiniteMeasure_leadingResidueMeasureU Y hμ (Ξ.chartLeading_of_extremalData Y h hc)
  refine ⟨?_⟩
  rw [Ξ.extremalStratumMeasure_univ Y h hc hμ hm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-! ### The global extremal stratum measure on `U` -/

/-- ★★★ **The global extremal stratum measure** on `U`: the pushforward of `ν^{λ*}_{m*}` along
`X ↪ U`. -/
noncomputable def globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure Ξ.R.U :=
  (Ξ.extremalStratumMeasure Y h hm).map Subtype.val

/-- ★★★ **The global extremal stratum measure is the raw leading measure restricted to the open
stratum**: `Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}|_{U ∖ D_{m*+1}}`. -/
theorem globalExtremalStratumMeasure_eq_restrict {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm = ENNReal.ofReal (residueConst lam m) •
      (Ξ.leadingResidueMeasureU Y lam m).restrict (Ξ.stratumOpen m) := by
  unfold globalExtremalStratumMeasure
  rw [Ξ.extremalStratumMeasure_eq_leadingResidue Y h hc hμ hm, Measure.map_smul,
    leadingResidueMeasureX, map_comap_subtype_coe (Ξ.measurableSet_stratumOpen m)]

/-- ★★ **The raw leading measure is the global extremal stratum measure exactly when the deep
fibre is null**: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` on `U` iff
`ρ^{λ*}_{m*}(D_{m*+1} ∩ Z₀) = 0`. -/
theorem globalExtremalStratumMeasure_eq_iff {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
        ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m ↔
      Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0 := by
  rw [Ξ.globalExtremalStratumMeasure_eq_restrict Y h hc hμ hm]
  constructor
  · intro heq
    have hc0 : ENNReal.ofReal (residueConst lam m) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (residueConst_pos hμ m)).ne'
    have := congrArg (fun ν : Measure Ξ.R.U => ν (Ξ.deepZeroFibre m)) heq
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (Ξ.measurableSet_deepZeroFibre m)] at this
    rw [stratumOpen, inter_compl_self, measure_empty, mul_zero, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hc0
  · intro hnull
    rw [Measure.restrict_eq_self_of_ae_mem]
    exact compl_mem_ae_iff.2 hnull

/-- ★★★ **The global extremal stratum measure is the residue-constant multiple of the raw leading
measure on all of `U`**: `ν^{λ*}_{m*} = Γ(λ*)/(m*−1)! · ρ^{λ*}_{m*}` (the deep fibre is null). -/
theorem globalExtremalStratumMeasure_eq {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) • Ξ.leadingResidueMeasureU Y lam m :=
  (Ξ.globalExtremalStratumMeasure_eq_iff Y h hc hμ hm).2
    (Ξ.leadingResidueMeasureU_deepZeroFibre Y lam m)

/-- ★★★ **The coefficient functional at the extremal pair is the global extremal stratum measure
for EVERY smooth observable** (no test hypothesis). -/
theorem coeff_withF_eq_integral_globalExtremalStratumMeasure {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hc : Ξ.ExtremalCertificate Y) (hμ : 0 < lam) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).coeff Y lam (m - 1) =
      ∫ x, G x ∂(Ξ.globalExtremalStratumMeasure Y h hm) := by
  rw [Ξ.globalExtremalStratumMeasure_eq Y h hc hμ hm, integral_smul_measure,
    ENNReal.toReal_ofReal (residueConst_pos hμ m).le, smul_eq_mul]
  exact Ξ.coeff_withF_eq_integral_leadingResidueMeasureU Y h hc hμ hm hG

/-- The global extremal stratum measure integrates every smooth observable vanishing off the open
stratum to the coefficient functional. -/
theorem integral_globalExtremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (G : Ξ.R.U → ℝ) :
    ∫ x, G x ∂(Ξ.globalExtremalStratumMeasure Y h hm) =
      ∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm) :=
  (MeasurableEmbedding.subtype_coe (Ξ.measurableSet_stratumOpen m)).integral_map _

end ResolvedData

end SmoothEngine

end Grammar
```

---
# The current paper draft (grammar2 main.tex and sections, verbatim)
```latex
% Lean pins. Comments of the form '% Lean @ d56efc8: <file>: <declarations>' next to each result name the formal
% counterparts in timaeus-research/grammar at commit d56efc8 (namespaces written in full); '% Lean (bridge workspace ...
% @ 17c058b)' refers to lean/grammar-greybook-bridge, the statements about the sample on the grey book formalisation.
% '% Lean: not formalised' marks results that are analytic derivations without a formal counterpart.
\documentclass[11pt]{article}
\usepackage[margin=1.1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,calc,positioning,decorations.pathreplacing,shapes.geometric}
\usepackage{booktabs}
\usepackage{array}
\usepackage[round]{natbib}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=blue!60!black,citecolor=blue!60!black,urlcolor=blue!60!black}
\usepackage[capitalise,noabbrev]{cleveref}
\crefname{thm}{Theorem}{Theorems}
\crefname{prop}{Proposition}{Propositions}
\crefname{lem}{Lemma}{Lemmas}
\crefname{cor}{Corollary}{Corollaries}
\crefname{defn}{Definition}{Definitions}
\crefname{remark}{Remark}{Remarks}
\crefname{example}{Example}{Examples}
\crefname{equation}{}{}

\newtheorem{thm}{Theorem}[section]
\newtheorem{prop}[thm]{Proposition}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{cor}[thm]{Corollary}
\newtheorem{defn}[thm]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[thm]{Remark}
\newtheorem{example}[thm]{Example}

\DeclareMathOperator{\Cov}{Cov}
\DeclareMathOperator{\Var}{Var}
\newcommand{\E}{\mathbb E}
\newcommand{\R}{\mathbb R}
\newcommand{\N}{\mathbb N}
\newcommand{\Zcal}{\mathcal Z}
\newcommand{\Dn}{\mathcal D_n}
\newcommand{\Rres}{\mathcal R}
\newcommand{\Ical}{\mathcal I}
\DeclareMathOperator{\res}{res}

\title{Expectations and the Exceptional Divisor}
\author{Daniel Murfet}
\date{September 2026}

\begin{document}
\maketitle

\begin{abstract}
The expectation of an observable $f$ under the Bayesian posterior of a singular statistical model is the ratio $Z_n[f]/Z_n[1]$ of two partition functions with insertion. We give the complete asymptotic expansion of $Z_n[f]$ in the sample size $n$, for the population divergence and for the empirical loss of a fixed sample, and describe its coefficients without coordinates. After resolution of singularities the zero locus of the divergence becomes a normal crossing divisor with a stratification, and every coefficient is a distribution supported on the strata of the exceptional divisor whose walls resonate with its exponent, paired with the observable: at leading order a measure, the weighted logarithmic residue of the resolved integrand along the deepest stratum of lowest exponent, and at higher orders, on observables vanishing near the deeper crossings, the pairing of finitely many normal derivatives of the observable with residue data of higher order. The sample enters through Watanabe's standard form as a field on the resolution, and its whole effect is to replace the Gamma function in the stratum measures by the fluctuation function of the field along the stratum, with derivatives of the field entering the corrections through a ladder of indices. Posterior expectations are quotients of these expansions, and their coefficients are rational functions of the same data. The analysis is carried out for smooth priors and observables throughout, the running examples are worked in detail, and the statements have been formalised in the Lean theorem prover; a table records what is a theorem and under which hypotheses.
\end{abstract}

\tableofcontents

\part{The question and the geometry}
\input{sections/01_introduction}
\input{sections/02_setting}
\input{sections/03_resolution}
\input{sections/04_stratification}

\part{Population expectations, coordinate-free}
\input{sections/05_normal_geometry}
\input{sections/07_population}

\part{The data}
\input{sections/08_fluctuation}
\input{sections/09_empirical}
\input{sections/10_limit}

\part{Expectations}
\input{sections/11_posterior}
\input{sections/12_averaging}
\input{sections/13_formalisation}
\input{sections/14_conclusion}

\bibliographystyle{plainnat}
\bibliography{references}

\appendix
\input{sections/A_chart_proofs}
\input{sections/B_fluctuation_facts}
\input{sections/C_expansion_algebra}
\input{sections/D_resolution_facts}
\input{sections/E_moment_tensors}

\end{document}
```

## sections/01_introduction.tex
```latex
\section{Introduction}\label{sec:introduction}

A statistical model $p(x\mid w)$ with parameter $w\in W\subseteq\R^d$ fits a ground truth $q$ to the extent measured by the Kullback--Leibler divergence
\[
K(w)=\int q(x)\log\frac{q(x)}{p(x\mid w)}\,dx\,.
\]
Given $n$ samples $\Dn$ the Bayesian posterior concentrates near the zero locus $W_0=\{K=0\}$, and the point of view of singular learning theory \citep{watanabeAlgebraicGeometryStatistical2009,watanabe2018} is that the local geometry of $K$ along $W_0$ is where the information about what the model has learned resides. That geometry is not directly visible. What is visible, and what a growing body of empirical work actually measures, are posterior expectation values
\[
\E[f\mid\Dn]=\frac{Z_n[f]}{Z_n[1]},\qquad Z_n[f]=\int_W f(w)\,e^{-nL_n(w)}\,\varphi(w)\,dw ,
\]
of chosen observables $f$: the local learning coefficient estimator, susceptibilities of model components to perturbations of the data, per-sample influences. The question this paper answers is what a \emph{single} such expectation value sees.

As $n\to\infty$ the renormalised partition function with insertion has, for each sample, an asymptotic expansion
\begin{equation}\label{eq:intro_answer}
Z_n[f]\;\sim\;\sum_{\mu}\sum_{q}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q ,
\end{equation}
in which the candidate exponents $\mu$ and the powers of the logarithm are read off a resolution of the singularities of $K$ and do not depend on the sample, while each coefficient $c_{\mu,q}$ is a \emph{distribution supported on the strata of the exceptional divisor whose walls resonate with $\mu$}, paired with $f$; on observables that vanish near the deeper crossings it is represented by finitely many normal derivatives integrated over one stratum. Three actors appear in this formula, and the paper is organised around them.

\begin{itemize}
\item \textbf{The geometry.} Resolution of singularities replaces $W_0$ by a normal crossing divisor $E=E_1\cup\cdots\cup E_r$ on a manifold $U$ mapping onto $W$. Its components intersect along a stratification, and to each component are attached two integers: the order $2k_i$ to which $K$ vanishes along it and the order $h_i$ to which the prior measure does. The ratios $(h_i+1)/2k_i$ are the exponents; the strata along which several components meet with a common ratio are where the logarithms come from. Every coefficient in \eqref{eq:intro_answer} is a distribution supported on these strata; restricted to observables vanishing near the deeper crossings it is a measure, or a measure paired with finitely many normal derivatives, on one of them. This is the \emph{stratum measure} of the pair $(K,\varphi)$ at a given exponent and depth, and it is a coordinate-free object: the weighted logarithmic residue of the resolved integrand along the stratum.
\item \textbf{The observable.} The coefficients are linear in $f$. The leading coefficient pairs the stratum measure with the restriction of $f$ to the stratum; the corrections pair it with finitely many normal derivatives of $f$ along the stratum, of which the leading one is canonically a section of a symmetric power of the conormal bundle. An observable that vanishes along a stratum does not see it at the leading order and is instead seen at a shifted exponent, which is the mechanism by which different observables probe different parts of the singular locus.
\item \textbf{The data.} Replacing the population divergence $K$ by the empirical loss $L_n$ introduces a random field on the resolution, the standardised empirical process, and the whole effect of the sample on the expansion is that the Gamma function in the stratum measures is replaced by a \emph{fluctuation function} $S_\mu$ evaluated on that field along the stratum, with its derivatives entering the corrections in a rigid ladder. For a fixed sample the expansion is deterministic and the coefficients are functionals of finitely many jets of the field on the strata; as the sample grows the field converges to a Gaussian process and the coefficients converge with it.
\end{itemize}

Posterior expectations are quotients of two such expansions, for $f$ and for $1$, and therefore rational functions of the same coefficients. At leading order the posterior concentrates on the deepest strata of lowest exponent, weighted by the stratum measures and, in the empirical case, reweighted by the fluctuation function evaluated on the data. When several strata tie, the sample decides how the posterior mass is distributed between them.

None of this requires analyticity of the observable or of the prior, and the paper is written for smooth data throughout. The expansion, its coefficients, and the convergence of the top coefficients on admissible observables to their Gaussian limit, given that of the field's jets, have been formalised in the Lean theorem prover; a table of what is a theorem, with hypotheses, is given in \cref{sec:formalisation}, together with what is not.

\paragraph{Plan.} \cref{sec:setting} fixes the setting, the notion of asymptotic expansion in the scale $n^{-\mu}(\log n)^q$, and the running examples. \cref{sec:resolution,sec:stratification} introduce the resolution and the stratification of its exceptional divisor at a gentle pace. Part~II develops the population expansion: the normal geometry of a stratum and what in it is intrinsic (\cref{sec:normal_geometry}), and the stratum measures with the zeta function that organises all orders (\cref{sec:population}). Part~III introduces the data: the fluctuation function (\cref{sec:fluctuation}), the expansion for a fixed sample (\cref{sec:empirical}), and the Gaussian limit (\cref{sec:limit}). Part~IV treats expectations: the posterior quotient (\cref{sec:posterior}), averaging over the sample (\cref{sec:averaging}), and the formalisation (\cref{sec:formalisation}).

\paragraph{Notation.} $W\subseteq\R^d$ is the parameter space, $K$ the divergence, $L_n$ the empirical loss, $\varphi$ the prior density, $f$ an observable. $\Zcal_n[f]=\int f\,e^{-nK}\varphi\,dw$ is the population partition function with insertion and $Z_n[f]=\int f\,e^{-nL_n}\varphi\,dw$ the empirical one; $\pi\colon U\to W$ is the resolution, $E_i$ the components of the exceptional divisor with data $(k_i,h_i)$, $S_I=\bigcap_{i\in I}E_i\setminus\bigcup_{j\notin I}E_j$ the strata, $\lambda_I=\min_{i\in I}(h_i+1)/2k_i$ the exponent of a stratum and $m_I$ its multiplicity. Near a stratum $(v,u)$ are tangential and normal coordinates. $S_\mu$ is the fluctuation function and $\zeta$ the field on the resolution.
```

## sections/02_setting.tex
```latex
\section{Setting and the running examples}\label{sec:setting}

\subsection{Partition functions with insertion}

The parameter space $W\subseteq\R^d$ is compact with nonempty interior, cut out by finitely many real analytic inequalities and equal to the closure of its interior (a zero of $K$ lying only in a lower-dimensional piece of $W$ would contribute nothing to the integrals). The model $p(x\mid w)$ and the truth $q(x)$ are probability densities with a common support, and the truth is realisable: $W_0=\{w\in W: K(w)=0\}$ is nonempty. We assume $K$ is real analytic on a neighbourhood of $W$ and nonnegative there, as a divergence is, not identically zero on any connected component of the interior of $W$, with $W_0$ meeting the support of the prior; and that the prior $\varphi\ge0$ is smooth with compact support and positive on a neighbourhood of $W_0$. Exponents are always minimised over the walls that meet the support of the prior. The observables $f$ are smooth functions on a neighbourhood of $W$. Nothing in the paper requires $\varphi$ or $f$ to be analytic, and \cref{sec:resolution} explains why $K$ is the one function for which analyticity is used.

The population partition function with insertion and the corresponding expectation are
\[
\Zcal_n[f]=\int_W f(w)\,e^{-nK(w)}\varphi(w)\,dw,\qquad \E_\infty[f]=\frac{\Zcal_n[f]}{\Zcal_n[1]} .
\]
Given a sample $\Dn=\{x_1,\dots,x_n\}$ from $q$, the empirical loss $L_n(w)=-\frac1n\sum_i\log p(x_i\mid w)$ defines the empirical partition function with insertion and the Bayesian posterior expectation
\[
Z_n[f]=\int_W f(w)\,e^{-nL_n(w)}\varphi(w)\,dw,\qquad \E[f\mid\Dn]=\frac{Z_n[f]}{Z_n[1]} .
\]
The empirical divergence $K_n(w)=\frac1n\sum_i\log\frac{q(x_i)}{p(x_i\mid w)}$ satisfies $K_n=L_n+\frac1n\sum_i\log q(x_i)$ exactly, so replacing $L_n$ by $K_n$ multiplies numerator and denominator by the same sample-dependent constant; from now on $Z_n[f]=\int f\,e^{-nK_n}\varphi\,dw$ denotes this renormalised partition function. An inverse temperature $\beta$ in front of $nL_n$ changes nothing structurally and is absorbed into $n$ and into the field introduced below; we keep $\beta=1$.

\subsection{The standard form of the empirical divergence}

The difference between $K_n$ and $K$ is a fluctuation of order $n^{-1/2}$, but not uniformly: near $W_0$ the difference is itself small because the terms being summed are. Watanabe's standard form makes this precise. Define the empirical process
\[
\psi_n(w)=\frac1{\sqrt n}\sum_{i=1}^n\frac{K(w)-\log\big(q(x_i)/p(x_i\mid w)\big)}{\sqrt{K(w)}},\qquad w\notin W_0 ,
\]
so that, identically in $w\notin W_0$,
\begin{equation}\label{eq:standard_form}
K_n(w)=K(w)-\frac1{\sqrt n}\sqrt{K(w)}\,\psi_n(w) .
\end{equation}
The process $\psi_n$ has mean zero and is not defined on $W_0$ as written. Watanabe's standard-form theorem \citep[Main Theorem~6.1]{greybook} supplies, on each chart of the resolution of $K$ where $K\circ\pi=u^{2k}$, a smooth \emph{signed-root} representative $\xi_n$ with $K_n\circ\pi=u^{2k}-n^{-1/2}u^k\xi_n$; the field obtained by dividing by $\sqrt{K\circ\pi}=|u^k|$ is then smooth on each orthant of the normal coordinates and may jump in sign across an interior wall, which is why \cref{sec:empirical} works with orthantwise representatives. The representatives converge in law to a Gaussian process as $n\to\infty$. For the empirical results we assume in addition the statistical hypotheses of that theorem: the log-likelihood ratio $\log(q(x)/p(x\mid w))$ is analytic in $w$ with a holomorphic extension on a complex neighbourhood of $W$ whose $L^s(q)$ norms are controlled, and the relative finite variance condition; the population results of Part~II need only the geometric hypotheses above. Convergence of the normal derivatives of the field is a separate hypothesis, discussed in \cref{sec:limit}. Everything the sample does to the expansions of this paper is done through the exponent
\[
-nK_n=-nK+\sqrt n\,\sqrt K\,\psi_n ,
\]
and on the resolution, where $\sqrt{K\circ\pi}$ is a monomial, this is the exponent $-nu^{2k}+\sqrt n\,u^k\,\zeta(u)$ of a one-parameter family of integrals that we will analyse in complete generality. The field $\zeta$ is the sample; the rest is geometry.

\subsection{Asymptotic expansions in the scale \texorpdfstring{$n^{-\mu}(\log n)^q$}{n^-mu (log n)^q}}\label{sec:scale}

We follow \citet[Ch.~1]{paris2001asymptotics}. The functions $n^{-\mu}(\log n)^q$ with $\mu\in\mathbb Q_{>0}$ and $q\in\N$ are totally ordered by eventual domination: $n^{-\mu}(\log n)^q$ dominates $n^{-\mu'}(\log n)^{q'}$ when $\mu<\mu'$, or $\mu=\mu'$ and $q>q'$. We write $(\mu,q)\prec(\mu',q')$ in that case. For a locally finite set $\mathcal A\subseteq\mathbb Q_{>0}$ and $D\in\N$,
\[
F(n)\sim\sum_{\mu\in\mathcal A}\sum_{q=0}^{D}c_{\mu,q}\,n^{-\mu}(\log n)^q
\]
means that for every $(\mu',q')$ the difference $F(n)-\sum_{(\mu,q)\prec(\mu',q')}c_{\mu,q}n^{-\mu}(\log n)^q$ is $O(n^{-\mu'}(\log n)^{q'})$. Such an expansion, if it exists, determines its coefficients uniquely, and adding a term $O(e^{-\varepsilon n})$ changes nothing. All expansions in this paper have the additional property that the exponents lie on a lattice $Q^{-1}\N$ for an integer $Q$ determined by the resolution, and the logarithmic degree is bounded by $d-1$. In that situation the expansion is equivalent to the family of \emph{cutoff estimates}
\begin{equation}\label{eq:cutoff}
F(n)=\sum_{\mu\in Q^{-1}\N,\ \mu<U}\ \sum_{q\le D}c_{\mu,q}\,n^{-\mu}(\log n)^q+O\big(n^{-U}(1+\log n)^{D}\big),\qquad U>0 ,
\end{equation}
one for each cutoff $U$, with coefficients independent of $U$. This is the form in which the theorems are stated and proved; it is also the form that the formalisation uses.

Two facts about expansions in this scale are used repeatedly and are recorded in \cref{app:expansion_algebra}: the product of two expansions is an expansion with the convolved coefficients, and the quotient of two expansions is an expansion provided the denominator's leading block, the polynomial in $\log n$ multiplying its lowest power of $n$, is nonzero. The quotient's coefficients are rational functions of $\log n$ whose numerators and denominators are built from the two coefficient systems by formal division in the variable $x=n^{-1/Q}$. Posterior expectations are such quotients.

\subsection{Comparability}

The divergence is analytic but rarely polynomial. Two nonnegative functions $g_1,g_2$ on an open set are \emph{comparable}, $g_1\asymp g_2$, if $c_1g_2\le g_1\le c_2g_2$ for positive constants. Comparable functions have the same vanishing orders along every component of a common resolution \citep[App.~B]{murfet2025programssingularities}, hence the same candidate exponents and logarithmic degrees and the same leading pair $(\lambda,m)$ for positive amplitudes, and in examples one replaces $K$ by a comparable polynomial when one exists; it need not, since $(y-e^x)^2$ has none. The coefficients change under such a replacement, and a subleading candidate term that is present for one phase may be absent for a comparable one.

\subsection{The running examples}\label{sec:examples}

Two examples accompany the whole paper. Both have a divergence that is already a monomial, so that the resolution is the identity and the geometry can be seen without any machinery; \cref{sec:resolution} adds an example where a blow-up is genuinely needed.

\begin{example}[Two planes meeting along a line]\label{ex:planes}
Let $W=[-1,1]^3$ with coordinates $(x,y,z)$ and $K(x,y,z)=x^2y^2$, with a smooth positive prior $\varphi$. The zero locus is the union of the two planes $\{x=0\}$ and $\{y=0\}$, meeting along the $z$-axis. Along each plane $K$ vanishes to order $2$ and the prior measure to order $0$, so each carries the ratio $1/2$; along the axis both planes meet with the same ratio. We will see that $\Zcal_n[1]\sim C\,n^{-1/2}\log n$, that the logarithm is the signature of the axis, and that the leading coefficient is an integral of the prior along the axis: the posterior concentrates on the line $\{x=y=0\}$. An observable $f(x,y,z)$ is seen at leading order only through its restriction to the axis, $f(0,0,z)$; an observable vanishing on the axis, such as $f=x^2$, loses the logarithm without changing the exponent, and is seen on the plane $\{y=0\}$, where it does not vanish, through its restriction to that plane.
\end{example}

\begin{example}[Mixed exponents]\label{ex:mixed}
Let $W=[0,1]^2$, a model whose two parameters are constrained to be nonnegative, with $K(x,y)=x^2y^6$. The two lines $\{x=0\}$ and $\{y=0\}$ are now walls of the parameter space and carry the ratios $1/2$ and $1/6$. The line $\{y=0\}$ leads, alone, so $\Zcal_n[1]\sim C\,n^{-1/6}$ with no logarithm. The first candidate correction sits at $n^{-1/3}$, carried by $\{y=0\}$ alone through the first normal derivative of the amplitude; the next candidate exponent is $n^{-1/2}$, where the line $\{x=0\}$ first resonates and a logarithm is allowed, present when the second $y$-derivative of the amplitude at the origin is nonzero. Whether a candidate term is present depends on the amplitude: for a constant amplitude one has exactly $\Zcal_n[1]=\frac{\Gamma(1/6)}4n^{-1/6}-\frac{\Gamma(1/2)}4n^{-1/2}+O(e^{-\varepsilon n})$, with neither an $n^{-1/3}$ term nor a logarithm. This example exhibits the three tiers of \cref{sec:population} in sequence. The nonnegativity constraint matters: on a symmetric domain such as $[-1,1]^2$ the odd normal moments of the population integral cancel between the two sides of a wall and the $n^{-1/3}$ candidate vanishes for every amplitude (\cref{rem:parity}).
\end{example}

In both examples the strata are the axis and the two planes, or the two lines and the origin; the observable enters through its restriction to them and its normal derivatives; and once the sample is introduced, the field enters through the fluctuation function on the leading stratum.
```

## sections/03_resolution.tex
```latex
\section{Resolution and the exceptional divisor}\label{sec:resolution}

The integrals $\Zcal_n[f]$ concentrate, as $n\to\infty$, on the zero locus $W_0$ of $K$, and their asymptotics are governed by how $K$ vanishes there. In general $W_0$ is a singular set and $K$ vanishes along it in an intricate way. Resolution of singularities is the device that replaces this situation by a standard one: after a proper change of variables $\pi\colon U\to W$, the function $K\circ\pi$ vanishes along a union of smooth hypersurfaces meeting transversally, and near every point it is a monomial in suitable coordinates. This section states the resolution theorem in the form we use and explains what the local picture looks like.

\subsection{The theorem}

We work with the complexification: $K$ is the restriction to $W$ of a holomorphic function $K_{\mathbb C}$ on an open set $W^{(\mathbb C)}\subseteq\mathbb C^d$ containing $W$ \citep[Fundamental Condition~I]{watanabe2018}. By Hironaka's theorem \citep{hironaka1964resolution1,bierstone1997canonical}, in the form given by \citet[\S11.3]{igusa2000introduction}, there exist a $d$-dimensional complex manifold $U_{\mathbb C}$, a proper holomorphic map $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$ which is an isomorphism over the complement of $\{K_{\mathbb C}=0\}$ (when the boundary functions of $W$ are resolved simultaneously, as in \cref{app:resolution_facts}, the exceptional locus also contains the singular locus of the boundary, and the Jacobian orders $h_i$ below include the effect of rectilinearising the domain), and a finite set of smooth closed hypersurfaces $E_1,\dots,E_r$ of $U_{\mathbb C}$ with normal crossings, such that
\[
(K_{\mathbb C}\circ\pi)^{-1}(0)=E_1\cup\cdots\cup E_r
\]
and, at every point of this set through which exactly the components $E_1,\dots,E_p$ pass, there are local coordinates $(u_1,\dots,u_d)$ in which $E_i=\{u_i=0\}$ and
\begin{equation}\label{eq:local_normal_form}
K_{\mathbb C}\circ\pi=\varepsilon\,\prod_{i=1}^pu_i^{a_i},\qquad \pi^*(dw_1\cdots dw_d)=b\,\prod_{i=1}^pu_i^{h_i}\,du_1\cdots du_d ,
\end{equation}
with $\varepsilon,b$ nonvanishing holomorphic functions and integers $a_i>0$, $h_i\ge0$ attached to the components. The pair $(a_E,h_E)$ depends only on the component $E$: $a_E$ is the order to which $K\circ\pi$ vanishes along $E$ and $h_E$ the order to which the Jacobian of $\pi$ does.

Since $K$ has real coefficients the resolution can be built from blow-ups along real centres, and then $U_{\mathbb C}$ carries an anti-holomorphic involution lifting complex conjugation whose fixed locus $U=U_{\mathbb R}$ is a real manifold of dimension $d$ with $\pi\colon U\to W^{(\mathbb R)}$ a proper real analytic map. The components that matter are those whose real points form real hypersurfaces; a pair of conjugate components meeting at a real point, as for $x^2+y^2$, is not yet of this form, and the real resolution continues with real blow-ups until every component through a real point is a real hypersurface, at which point the coordinates in \eqref{eq:local_normal_form} can be taken real \citep[Thm~2.3]{watanabeAlgebraicGeometryStatistical2009}. Nonnegativity of $K$ forces every exponent $a_i$ to be even, $a_i=2k_i$, and $\varepsilon>0$ near the real points; absorbing $\varepsilon^{1/2k_1}$ into $u_1$ we may take $\varepsilon=1$. So the local picture on the real resolution is
\begin{equation}\label{eq:real_normal_form}
K\circ\pi=\prod_{i=1}^pu_i^{2k_i},\qquad \pi^*(\varphi\,dw)=g(u)\prod_{i=1}^p|u_i|^{h_i}\,du ,
\end{equation}
with $g=|b|\,(\varphi\circ\pi)$ smooth, and nonnegative where $\varphi$ is. This is the only place where analyticity is used: it is needed for the resolution of $K$, and for nothing else. The prior enters through $g$, which is smooth, and so does the observable, through $f\circ\pi$.

\input{figures/resolution_schematic}

\subsection{The two divisors}

The formula \eqref{eq:real_normal_form} records two different divisors on $U$. The first is the divisor of $K\circ\pi$, with multiplicities $2k_i$: it says how fast the Boltzmann weight $e^{-nK\circ\pi}$ decays away from the components. The second is the divisor of the pulled-back measure $\pi^*(\varphi\,dw)$, with multiplicities $h_i$: it says how much volume the change of variables has compressed onto each component. The asymptotics of $\int e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ near a component is a competition between the two, and the outcome of the competition in one normal variable is the elementary integral
\begin{equation}\label{eq:one_variable}
\int_0^1u^{h}\,e^{-nu^{2k}}\,du=\frac{1}{2k}\,\Gamma\!\Big(\frac{h+1}{2k}\Big)\,n^{-\frac{h+1}{2k}}+O(e^{-n/2}) ,
\end{equation}
obtained by the substitution $t=nu^{2k}$. The exponent $(h+1)/2k$ is the number attached to a component of the divisor; the smaller it is, the slower the decay, and the more the component contributes. When several components pass through a point the phase is the product $\prod_iu_i^{2k_i}$ and the local integral no longer factors, but its Mellin transform in $n$ does, into $\Gamma(s)$ times one-variable factors $\int u_i^{h_i-2k_is}\,du_i$, so that the exponents combine as poles of the Mellin transform rather than as numbers: this is where the logarithms come from, and it is the subject of \cref{sec:stratification}.

The vanishing orders $h_i$ are the reason the prior cannot be dropped from the picture. Changing the prior does not change the components or the $k_i$, but a prior vanishing to finite monomial order along part of $W_0$ changes the $h_i$ there and hence the exponents (a smooth prior may also vanish flatly or on a non-analytic set, which no integer divisor records; under the standing hypothesis that the prior is positive near $W_0$ the question does not arise). In the same way an observable $f$ vanishing to order $l_i$ along $E_i$ shifts the second divisor for the integral $\Zcal_n[f]$ to $h_i+l_i$, which is the mechanism of \cref{sec:wallcrossing}.

\subsection{Irreducible components as primes}

The components $E_i$ are canonical once the resolution is fixed: working with the Zariski topology on $U_{\mathbb C}$, the zero locus of $K_{\mathbb C}\circ\pi$ has a unique decomposition into irreducible components, and by the normal crossing property each is smooth. The analogy to keep in mind is the factorisation of an integer into primes: the components are the primes of the singularity, the multiplicities $2k_i$ are the exponents in the factorisation, and $h_i$ is a second numerical invariant of each prime. Different components represent independent ways in which the model attains zero divergence, and the intersection pattern records how these ways combine. We work over $\mathbb C$ for this decomposition because real analytic sets do not in general admit one \citep{fernando2016irreducible}; the real strata used in the integrals are the real points of the complex ones.

\subsection{An example with a blow-up}\label{ex:blowup}

The running examples of \cref{sec:examples} are already in the form \eqref{eq:real_normal_form}. To see what a resolution does, take $K(x,y)=x^2(x^2+y^2)$ on a neighbourhood of the origin in $\R^2$. Its zero locus is the line $\{x=0\}$, along which $K$ vanishes to order two except at the origin, where it vanishes to order four; since $x^2+y^2$ is not a product of real linear forms, no change of coordinates makes $K$ a monomial near the origin, and a blow-up is genuinely needed. Blowing up the origin replaces it by a projective line $E_0$. In the chart $y=u,\ x=uv$,
\[
K\circ\pi=u^2v^2\big(u^2v^2+u^2\big)=u^4v^2(1+v^2),\qquad dx\,dy=|u|\,du\,dv ,
\]
so $E_0=\{u=0\}$ carries $(k_0,h_0)=(2,1)$ and the strict transform $E_1=\{v=0\}$ of the line $\{x=0\}$, the closure of the preimage of the line with the origin removed, carries $(k_1,h_1)=(1,0)$; the other chart $x=u,\ y=uv$ gives $K\circ\pi=u^4(1+v^2)$ and shows $E_0$ alone. The two components meet in the single point $(u,v)=(0,0)$ of the first chart, $K\circ\pi$ is a monomial times a unit near it, and the singular point of $W_0$ has become a curve $E_0$ with one marked point where it meets the rest of the line. The ratios are $(h_0+1)/2k_0=1/2$ on $E_0$ and $(h_1+1)/2k_1=1/2$ on $E_1$: they tie, and the marked point, where two components of the same ratio meet, carries a logarithm, $\Zcal_n[1]\sim C\,n^{-1/2}\log n$. Nothing in the picture of $W_0$, a smooth line, announces this; the resolution reveals that the origin is more singular than the rest of the line. An observable vanishing at the origin of $W$ vanishes along all of $E_0$ after pull-back, since $\pi(E_0)$ is the origin; for $f=x^2+y^2$ the order is two, $E_0$ moves to the ratio $(1+2+1)/4=1$, the tie is broken, and $\Zcal_n[x^2+y^2]\sim C'n^{-1/2}$ without a logarithm, so that $\E_\infty[x^2+y^2]\sim C''/\log n$. An observable vanishing along the line $\{x=0\}$ itself vanishes along both $E_1$ and $E_0$, and the minimum and its multiplicity must be recomputed at the marked point.
```

## sections/04_stratification.tex
```latex
\section{The stratification of the exceptional divisor}\label{sec:stratification}

The exceptional divisor $E=E_1\cup\cdots\cup E_r$ is not a manifold: it is a union of manifolds that cross. The natural way to organise it is by how many components pass through a point. This section introduces the resulting stratification, which is the index set of everything that follows, and explains which strata carry the leading behaviour and why.

\subsection{Depth and strata}

For a point $u\in E$ let $I(u)=\{i: u\in E_i\}$ be the set of components through $u$; its size is the \emph{depth} of $u$. For a nonempty $I\subseteq\{1,\dots,r\}$ set
\[
E_I=\bigcap_{i\in I}E_i,\qquad S_I=E_I\setminus\bigcup_{j\notin I}E_j ,
\]
so that $S_I$ is the set of points through which exactly the components indexed by $I$ pass. By the normal crossing property $E_I$ is a smooth submanifold of codimension $|I|$ (or empty) and $S_I$ is open in it. The $S_I$ are the \emph{strata}; they are disjoint, they cover $E$, and the closure of $S_I$ is the union of the $S_J$ with $J\supseteq I$. Ordering by depth gives a filtration by closed sets
\[
E=D_1\supseteq D_2\supseteq\cdots\supseteq D_d,\qquad D_c=\{u\in E:\operatorname{depth}(u)\ge c\}=\bigcup_{|I|\ge c}E_I ,
\]
whose successive differences $D_c\setminus D_{c+1}$ are the unions of the strata of depth $c$. This is a stratification in the sense of \citet{trotmanstrat}, and a particularly well-behaved one: in the local coordinates \eqref{eq:real_normal_form} a stratum of depth $p$ is a coordinate subspace $\{u_1=\cdots=u_p=0\}$ and its normal directions are the coordinate directions $u_1,\dots,u_p$, each labelled by a component and carrying that component's data $(k_i,h_i)$.

In \cref{ex:planes} the strata are the two planes with the axis removed, of depth one, and the axis, of depth two. In \cref{ex:mixed} they are the two lines with the origin removed and the origin. In \cref{ex:blowup} they are the exceptional curve $E_0$ and the strict transform $E_1$ with their common point removed, and that point. The picture to hold on to is a cell decomposition of $E$ in which cells of higher depth lie in the closures of cells of lower depth, and the deepest cells, where the most components meet, are the smallest.

\input{figures/stratification}
\input{figures/planes}

\subsection{Exponents and multiplicities of a stratum}

Near a point of $S_I$ with normal coordinates $u=(u_i)_{i\in I}$ and tangential coordinates $v$ along the stratum, the integrand of $\Zcal_n[f]$ is
\[
(f\circ\pi)(v,u)\;\prod_{i\in I}|u_i|^{h_i}\;e^{-n\prod_{i\in I}u_i^{2k_i}}\;g(v,u)\,du\,dv .
\]
Freezing $v$, the $u$-integral is a $|I|$-dimensional version of \eqref{eq:one_variable}. Its behaviour is governed by the ratios attached to the normal directions,
\[
\lambda_i=\frac{h_i+1}{2k_i}\quad(i\in I),\qquad \lambda_I=\min_{i\in I}\lambda_i,\qquad m_I=\#\{i\in I:\lambda_i=\lambda_I\} ,
\]
and the basic fact, proved in \cref{sec:population}, is that the $u$-integral is asymptotic to a constant times $n^{-\lambda_I}(\log n)^{m_I-1}$. The exponent of a stratum is the smallest ratio among its normal directions; the multiplicity is the number of normal directions attaining it, and the multiplicity less one is the largest power of the logarithm that can occur; whether it does depends on the amplitude, and a positive amplitude guarantees it. A stratum where all normal directions share the same ratio is called \emph{tied} at that exponent; it is the zero-order case of the exact strata of \cref{sec:exact_strata}, and the deepest tied strata at the smallest exponent are where the leading term of $\Zcal_n[1]$ lives.

The mechanism behind the logarithm is worth seeing once in coordinates, and it rests on one classical fact. The Mellin transform of a function $F$ on $(0,\infty)$ is $\int_0^\infty n^{s-1}F(n)\,dn$. For $F(n)=\Zcal_n[1]$ it converges for $0<\operatorname{Re}s<\lambda$, equals $\Gamma(s)\int_WK^{-s}\varphi\,dw$ by Fubini, and continues meromorphically to the plane; a term $c\,n^{-\mu}(\log n)^q$ in the expansion of $F$ corresponds to a pole of order $q+1$ at $s=\mu$, and the poles of the continuation in $\operatorname{Re}s>0$, with their orders and Laurent coefficients, determine the expansion \citep[Ch.~4]{watanabeAlgebraicGeometryStatistical2009}; the possible poles of $\Gamma(s)$ at the nonpositive integers record the behaviour of $F$ at small $n$, not its asymptotics. The correspondence is made exact in \cref{sec:tiers}. With two normal directions of equal ratio $\lambda$, the Mellin transform of the $u$-integral is a product of two factors each with a simple pole at $s=\lambda$, and a double pole corresponds to a term $n^{-\lambda}\log n$. With different ratios the poles are at different places and the smaller one wins with no logarithm. In \cref{ex:planes} the axis has two normal directions with ratio $1/2$, so $\lambda=1/2$, $m=2$ and $\Zcal_n\sim Cn^{-1/2}\log n$; each plane has a single normal direction with ratio $1/2$ and contributes $n^{-1/2}$ without a logarithm, which is dominated. In \cref{ex:mixed} the origin has normal directions with ratios $1/2$ and $1/6$, so $\lambda=1/6$ and $m=1$, while the line $\{y=0\}$ has the single ratio $1/6$: the leading term $n^{-1/6}$ is carried by the line, and the origin is not exact at $1/6$.

The global exponents of $\Zcal_n[1]$ are
\[
\lambda=\min_I\lambda_I,\qquad m=\max\{m_I:\lambda_I=\lambda\} ,
\]
the real log canonical threshold and its multiplicity \citep{watanabeAlgebraicGeometryStatistical2009}; the exact strata at $(\lambda,m)$, those of depth $m$ all of whose walls have exponent $\lambda$, carry the leading coefficient, which is a sum of integrals over them; a deeper point on the closure of such a stratum, like the origin of \cref{ex:mixed}, has $\lambda_I=\lambda$ but contributes no atom of its own. The whole expansion \eqref{eq:intro_answer} arises in the same way from all strata and all their normal directions: every exponent that occurs is of the form $(h_i+\alpha+1)/2k_i$ for some component $E_i$ and some $\alpha\in\N$, the shift $\alpha$ being the order of a normal derivative of the amplitude, and a stratum contributes at an exponent $\mu$ precisely when each of its normal directions resonates with $\mu$ in this sense. The exponents therefore lie on the lattice $Q^{-1}\N$ with $Q=2\prod_ik_i$, and the logarithmic degree at $\mu$ is bounded by the largest depth of a stratum all of whose normal directions resonate with $\mu$.

\input{figures/mixed}

\subsection{Wall-crossing}\label{sec:wallcrossing}

Now insert an observable. Suppose that in signed normal coordinates $f\circ\pi=\prod_{i\in I}u_i^{l_i}\tilde f$ near $S_I$ with $\tilde f$ smooth and not identically zero on $S_I$. This is a hypothesis on $f$, stronger than prescribing the vanishing order of $f\circ\pi$ along each wall separately: $f=x^2+y^2$ has order zero along both axes of $x^2y^2$ but vanishes at their crossing, and a smooth observable may also vanish to infinite order, in which case the stratum contributes nothing at any algebraic order. Then the integrand of $\Zcal_n[f]$ near $S_I$ has the form of the integrand of $\Zcal_n[1]$ with $h_i$ replaced by $h_i+l_i$, up to the sign of $u_i^{l_i}$ on the two sides of an interior wall. The candidate exponents of the stratum shift:
\[
\lambda_I(f)=\min_{i\in I}\frac{h_i+l_i+1}{2k_i}\ \ge\ \lambda_I ,
\]
with equality if and only if $l_i=0$ for some $i$ attaining the minimum, and the multiplicity $m_I(f)$ is recomputed with the shifted ratios. These are candidate first terms: the coefficient at the shifted pair is an integral of $\tilde f$ against a density on the stratum, and it can vanish for a signed $\tilde f$, or by the parity cancellation of \cref{rem:parity}; a nonnegative $\tilde f$ positive somewhere on the stratum where the prior is positive makes it nonzero provided the orders $l_i$ are even in every interior direction, since otherwise the sign of $u_i^{l_i}$ cancels between the two sides ($f=x$ for $K=x^2$ on $[-1,1]$ has $\tilde f=1$ and $\Zcal_n[x]=0$). With this caveat, an observable that vanishes along a component is blind to the strata whose leading behaviour that component carries: it either loses the logarithm, if the component was one of several tied at the minimum, or moves to a higher exponent, if the component carried the minimum alone. If $f$ vanishes along every wall of exponent $\lambda$ the candidate exponent of $\Zcal_n[f]$ is strictly larger than that of $\Zcal_n[1]$, and $\E_\infty[f]\to0$ at a rate that measures the order of vanishing.

This is the sense in which different observables probe different parts of the singular locus. In \cref{ex:planes}, $f=1$ and any $f$ with $\int f(0,0,z)\varphi(0,0,z)\,dz\ne0$ have exponent $1/2$ with a logarithm, carried by the axis (for $f=z$ and a symmetric prior the axis average vanishes and the logarithm is lost); $f=x^2$ vanishes to order two on the plane $\{x=0\}$ and hence on the axis, and the shifted ratios on the axis are $(0+2+1)/2=3/2$ for the $x$-direction and $1/2$ for the $y$-direction, so the axis now has exponent $1/2$ with multiplicity one, while the plane $\{y=0\}$, on which $f=x^2$ does not vanish, still has exponent $1/2$ with multiplicity one: $\Zcal_n[x^2]\sim Cn^{-1/2}$ with no logarithm, and $\E_\infty[x^2]\sim C'/\log n$. The posterior concentrates on the axis, and this is the rate at which it does so. In \cref{ex:blowup}, an observable vanishing at the origin of $W$ shifts the exceptional curve $E_0$; whether this breaks the tie at the marked point depends on the orders ($f=x^2+y^2$ breaks it, while $f=K$ shifts both ratios to $3/2$ and does not), and an observable vanishing along the line $\{x=0\}$ shifts both $E_1$ and $E_0$.

\begin{remark}[Parity]\label{rem:parity}
A component $E_i$ either resolves a wall of the parameter space, in which case the normal coordinate $u_i$ runs over a one-sided interval $[0,\varepsilon)$, or lies in the interior of $U$, in which case $u_i$ runs over $(-\varepsilon,\varepsilon)$. In the second case the population normal integral is a sum over the two sides, and the amplitude is replaced by its even part in $u_i$: all odd normal derivatives in an interior direction drop out of the population expansion, and only even shifts $\alpha$ survive. \cref{ex:planes} has interior components, so its population corrections proceed in steps of $2$ in each normal direction; \cref{ex:mixed} has boundary components, and all shifts are candidates. In the empirical expansion of Part~III the cancellation requires in addition that the field's orthantwise representatives be compatible under the reflection, since an odd derivative of the amplitude can couple to the odd part of the field's exponential; without that symmetry odd candidates survive. The chart-level statements of Parts~II and~III are formulated on the positive box, where both cases are covered by summing over the orthants.
\end{remark}

A remark on what is intrinsic. The candidate exponents and multiplicities read off a resolution are not invariant: a further blow-up adds components and hence candidates (blowing up the axis of \cref{ex:planes} adds a component with $(k,h)=(2,1)$ and the candidates $(2+\alpha)/4$), which then cancel. What is invariant is the expansion itself, its nonzero coefficients and in particular the leading pair; the coefficients we construct in Part~II are pairings of $f$ with measures on the strata, and \cref{sec:population} explains in what sense those measures are independent of the choices made in constructing them. The stratification is scaffolding of the same kind as the coordinates: canonical once $\pi$ is fixed, and used to organise a computation whose outcome is a distribution on $W_0$.
```

## sections/05_normal_geometry.tex
```latex
\section{The normal geometry of a stratum}\label{sec:normal_geometry}

The coefficients of the expansion will be integrals over strata of normal derivatives of the amplitude. This section fixes what normal means near a stratum of the exceptional divisor, reduces the integral near a stratum to fibre integrals whose asymptotics carry the exponents and logarithms, and states which parts of the resulting description are independent of coordinates. The tubular neighbourhoods and moment tensors of the earlier account of this material are not needed for the proofs and are recorded in \cref{app:moment_tensors}.

\subsection{Normal and tangential coordinates}

Let $S=S_I$ be a stratum. By the normal crossing property, near a point of $S$ there are coordinates $(v,u)$ with $u=(u_i)_{i\in I}$ in which $E_i=\{u_i=0\}$ for $i\in I$, $S=\{u=0\}$, and \eqref{eq:real_normal_form} holds: the normal coordinates are labelled by the components through the stratum, each carrying that component's data $(k_i,h_i)$, and $v$ are coordinates along $S$. Another choice of coordinates of this kind replaces each $u_i$ by a unit multiple $u_i'=g_iu_i$, with $g_i$ a nonvanishing smooth function of all the coordinates, and $v$ by other coordinates along $S$. This is the only freedom, and it is what the coordinate-free statements of \cref{sec:conormal} have to survive.

Along $S$ the differentials $du_i$ span the conormal bundle $N^*S\subseteq T^*U|_S$, the covectors that kill $TS$, and since $du_i'=g_i\,du_i$ on $S$ the line $\mathcal L_i$ spanned by $du_i$ depends only on the component $E_i$. Hence, canonically,
\begin{equation}\label{eq:conormal_splitting}
N^*S=\bigoplus_{i\in I}\mathcal L_i,\qquad \operatorname{Sym}^r(N^*S)=\bigoplus_{|b|=r}\ \bigotimes_{i\in I}\operatorname{Sym}^{b_i}(\mathcal L_i) :
\end{equation}
a stratum knows which of its normal directions belongs to which component, which is what allows the data $(k_i,h_i)$ of the components to be attached to normal directions of the stratum.

\subsection{The fibre integral and the bare moments}

Near $S$ the integrand of $\Zcal_n[f]$ is, in the notation of \eqref{eq:real_normal_form},
\[
(f\circ\pi)\;e^{-n(K\circ\pi)}\;\pi^*(\varphi\,dw)=(f\circ\pi)(v,u)\;|u|^{h_I}\;e^{-nu^{2k_I}}\;g(v,u)\,|du\,dv| ,
\]
where $u^{2k_I}=\prod_{i\in I}u_i^{2k_i}$, $|u|^{h_I}=\prod_{i\in I}|u_i|^{h_i}$, and $g$ is the smooth factor of \eqref{eq:real_normal_form}, the prior times the smooth part of the Jacobian. Freezing $v$, the contribution of a neighbourhood of the stratum is an integral over $S$ of the fibre integrals
\begin{equation}\label{eq:fibre_integral}
\int_{D_v}(f\circ\pi)(v,u)\,|u|^{h_I}\,e^{-nu^{2k_I}}\,g(v,u)\,du ,
\end{equation}
in which $v$ is a parameter and $D_v$ is a box in the normal variables, one-sided in each direction whose component resolves a wall of $W$ and two-sided in each interior direction. Expanding the amplitude $(f\circ\pi)\,g$ in a finite Taylor series in $u$ at $u=0$ turns \eqref{eq:fibre_integral} into a combination of \emph{bare normal moments}
\begin{equation}\label{eq:bare_moment}
M_\alpha(n)=\int_{D}u^\alpha\,|u|^{h_I}\,e^{-nu^{2k_I}}\,du ,
\end{equation}
which are the objects whose asymptotics carry the exponents and logarithms (\cref{sec:population}), plus a remainder. The tangential variable $v$ is inert: it appears only as a parameter in the amplitude, and the outer integral over $S$ is performed last. And over a two-sided direction the odd moments vanish, which is the source of the parity phenomenon of \cref{rem:parity}.

\begin{remark}[Why the crossing does not see everything]\label{rem:flat}
The remainder of the normal Taylor expansion is not negligible in general. It is small near $u=0$, but not along the adjacent walls $\{u_i=0\}$, where the phase $u^{2k_I}$ still vanishes and the Boltzmann weight does not decay. For $K=x^2y^2$ and $S$ the crossing, an amplitude flat at the origin but nonzero on the axis $\{y=0,\ x>0\}$ has every normal Taylor coefficient at the crossing equal to zero, yet contributes a nonzero $n^{-1/2}$ term from the axis. The contributions along the walls belong to the shallower strata, and the bookkeeping that does produce an asymptotic expansion expands the amplitude in the normal directions of each face of the chart cube and subtracts along the face what has already been counted at deeper faces. That is the face construction of \cref{sec:population} and \cref{app:chart_proofs}, from which every coefficient statement of this paper is derived.
\end{remark}

\begin{remark}[Cutoffs]\label{rem:cutoff}
Restricting the fibre to a bounded domain $D_v$ is harmless in one sense and not in another. Localising in the \emph{phase}, to the sublevel set $\{K\circ\pi<\varepsilon\}$, costs $O(e^{-n\varepsilon})$, which is invisible in the scale. Changing the \emph{normal} cutoff, say from $[0,b]^{|I|}$ to $[0,b']^{|I|}$, is not exponentially small, because $u^{2k_I}$ vanishes on the coordinate hyperplanes and the Boltzmann weight does not decay there. Such a change alters the coefficients of the expansion but not its exponents or logarithmic degrees. The coordinate-free formulation of \cref{sec:population} absorbs the cutoff into the partition of unity and makes the total coefficient, summed over strata, independent of these choices.
\end{remark}

\subsection{What is intrinsic}\label{sec:conormal}

Let $\Ical_S$ be the ideal of smooth functions vanishing on $S$. The class of a function $F$ modulo $\Ical_S^{\,r+1}$ is its \emph{transverse $r$-jet} along $S$; in coordinates of the kind above it is the collection of normal Taylor coefficients of $F$ through order $r$, by Hadamard's lemma, and the class itself does not depend on the coordinates. The associated graded is canonical and is the conormal bundle:
\[
\Ical_S^{\,r}/\Ical_S^{\,r+1}\;\cong\;\Gamma\big(S,\operatorname{Sym}^r(N^*S)\big) ,
\]
the leading normal Taylor coefficient of a function vanishing to order $r$ along $S$ being a symmetric $r$-form on the normal bundle, refined by \eqref{eq:conormal_splitting} according to how the order is distributed among the components. What is not canonical is the splitting of a jet into homogeneous pieces: under $u'=gu$ the normal derivatives of order $\beta$ of a function that does not vanish along $S$ pick up contributions from its lower-order derivatives.

The coefficients of the expansion have the following shape. In a normal crossing chart the coefficient at $(\mu,q)$ is a finite sum, over faces of the chart cube, of integrals over the face of normal derivatives of the localised amplitude against explicit densities (\cref{app:chart_proofs}); collecting the terms at a stratum $S$, for an amplitude vanishing near the deeper strata, gives a functional
\begin{equation}\label{eq:conormal_presentation}
F\;\longmapsto\;\sum_{|\beta|\le n}\int_S\partial^\beta_uF\;\rho_\beta ,
\end{equation}
with $\partial_u^\beta$ normal derivatives in the chart and $\rho_\beta$ densities on $S$: in the language of distributions, a \emph{conormal distribution} along $S$ of order $n$, supported on $S$ with singular structure transverse to it. Three things about this functional are proved in \cref{sec:population} and are independent of coordinates. Its support: the coefficient $c_{\mu,q}$ vanishes on observables that vanish near the set of points through which at least $q+1$ walls resonate with $\mu$. Its jet dependence: on observables vanishing near the deeper strata, the top coefficient at an exponent depends only on the transverse jet of a fixed order $n$ along the exact stratum (\cref{thm:jet}), so the functional descends to the quotient of such observables by the corresponding ideal power. And its principal symbol: restricted to observables that in addition vanish to order $n$ along the exact stratum, the functional factors through $\Ical_S^{\,n}/\Ical_S^{\,n+1}\cong\Gamma(S,\operatorname{Sym}^n(N^*S))$ by the previous point, and is therefore a coordinate-free pairing of the leading normal jet with a density on $S$ valued in $\operatorname{Sym}^n(NS)$, the top face density of \cref{thm:graded}. What is not canonical is the rest: the lower terms $\rho_\beta$, $|\beta|<n$, mix under a change of defining equations exactly as the lower Laurent coefficients of a pole of higher order do. Coordinates are therefore needed to \emph{write} a coefficient of positive normal order, and the writing is not unique; what is unique is the functional, the finite jet it depends on, and its principal symbol.

One special case makes the whole functional canonical: when $n=0$ the distribution is a measure on $S$, the stratum measure of \cref{sec:population}, the object through which the leading term and the top logarithmic coefficients are described. When $S$ is a single point the functional is a finite combination of derivatives of the delta function at that point; the combination is canonical as a distribution, while its individual coefficients depend on coordinates through the same mixing.
```

## sections/07_population.tex
```latex
\section{The stratum measures and the population expansion}\label{sec:population}

This section assembles the machinery into the expansion of $\Zcal_n[f]$ and describes its coefficients. The description proceeds from the coarse to the fine. First the exponents and logarithms, from the poles of a zeta function. Then the leading term at every exponent and depth, which is a measure on a stratum, canonical, and identified with a logarithmic residue of the resolved integrand. Then the corrections, organised as the Laurent data of one meromorphic function, with closed forms in the two situations that matter most. Throughout, $f$ and $\varphi$ are smooth; analyticity has been used once, for the resolution, and will not be used again.

\subsection{The per-stratum decomposition}

Pulling $\Zcal_n[f]$ back to the resolution is a change of variables, legitimate because $\pi$ is a diffeomorphism off a set of measure zero:
\[
\Zcal_n[f]=\int_U(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\]
Off the sublevel set $U_\varepsilon=\{K\circ\pi<\varepsilon\}$ the integrand is $O(e^{-n\varepsilon})$, invisible in the scale, so only a neighbourhood of $E$ matters. A smooth partition of unity $\sum_I\rho_I=1$ on $U_\varepsilon$ subordinate to a cover by normal crossing charts, each chart meeting only the components $E_i$ of one index set $I$ and each $\rho_I$ compactly supported in its chart, gives
% Lean @ d56efc8: Grammar/SmoothResolvedConsumer.lean: Grammar.SmoothEngine.ResolvedData (structure), Grammar.SmoothEngine.ResolvedData.coeff (def), Grammar.SmoothEngine.ResolvedData.coeff_eq_of_transports, Grammar.SmoothEngine.ResolvedData.coeff_comp_gv
% Lean @ d56efc8: Grammar/SmoothResolvedResonantSupport.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_eventually_zero_resonant
\begin{equation}\label{eq:strata_decomposition}
\Zcal_n[f]=\sum_I\Zcal_n[f;I]+O(e^{-n\varepsilon}),\qquad \Zcal_n[f;I]=\int\rho_I\,(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\end{equation}
The cutoffs depend on all chart coordinates and are simply part of the smooth amplitude that gets differentiated in the normal directions; no cutoff constant along fibres is needed or, in general, available. Each $\Zcal_n[f;I]$ is a chart integral of the form \eqref{eq:empirical_chart} at zero field. The individual terms $\Zcal_n[f;I]$ depend on the partition of unity; the sum does not, and neither do the candidate exponents and logarithmic degrees, which are read off the resolution data alone.

\subsection{The zeta function of a stratum and the shape of the expansion}

The asymptotics of a bare moment \eqref{eq:bare_moment} on the box $[0,b]^{|I|}$ are governed by the poles of
\[
\zeta_\gamma(z)=\int_{[0,b]^{|I|}}(u^{2k_I})^{z}\,u^{\gamma}\,|u|^{h_I}\,du=\prod_{i\in I}\frac{b^{2k_iz+h_i+\gamma_i+1}}{2k_iz+h_i+\gamma_i+1} ,
\]
a product of one-variable integrals because the integrand is a monomial. The $i$-th factor has a simple pole at $z=-(h_i+\gamma_i+1)/2k_i$, so $\zeta_\gamma$ has a pole at $z=-\lambda$ of order $m$ exactly when $m$ of the shifted ratios equal $\lambda$, and the Laplace transform relation $M_\gamma(n)=\int_0^\infty e^{-nt}\,d\nu_\gamma(t)$, with $\nu_\gamma$ the pushforward of $u^\gamma|u|^{h_I}du$ under $u\mapsto u^{2k_I}$, converts a pole of order $m$ at $-\lambda$ into a term $n^{-\lambda}(\log n)^{m-1}$ \citep[Ch.~4]{watanabeAlgebraicGeometryStatistical2009}. The leading Laurent coefficient is explicit: the factors with $i$ in the minimising set $J$ contribute $1/2k_i$ each and the others are evaluated at the pole,
% Lean @ d56efc8: Grammar/SmoothFaceMonoTop.lean: Grammar.SmoothEngine.faceMonoCoeff_top (equal-ratio case only: the constant Gamma(lam)/((m-1)! prod 2k_i); the complementary factors of the mixed-ratio display are a derivation)
\begin{equation}\label{eq:zeta_leading}
M_\gamma(n)\sim\frac{\Gamma(\lambda)}{(m-1)!}\ \prod_{i\in J}\frac1{2k_i}\ \prod_{i\in I\setminus J}\frac{b^{\,h_i+\gamma_i+1-2k_i\lambda}}{h_i+\gamma_i+1-2k_i\lambda}\ \ n^{-\lambda}(\log n)^{m-1} .
\end{equation}
The denominators in the second product are positive because $\lambda$ is the minimum; the factors of $1/2k_i$ are residues against $d\log u_i^{2k_i}$; and the factor $\Gamma(\lambda)/(m-1)!$ comes from the Laplace transform of $t^{\lambda-1}(\log t)^{m-1}$. All three ingredients reappear in the stratum measures below.

Combining \eqref{eq:zeta_leading} with the face construction of \cref{app:chart_proofs} and summing over strata gives the shape of the expansion, which we state now and refine through the rest of the section.

% Lean @ d56efc8: Grammar/SmoothGeneral.lean: Grammar.SmoothEngine.smooth_cutoffExpansion, Grammar.SmoothEngine.smoothCoeff_unique
% Lean @ d56efc8: Grammar/SmoothResolvedConsumer.lean: Grammar.SmoothEngine.ResolvedData.coeff, Grammar.SmoothEngine.ResolvedData.coeff_eq_of_transports, Grammar.SmoothEngine.ResolvedData.coeff_comp_gv
% Lean @ d56efc8: Grammar/SmoothResolvedResonantSupport.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_eventually_zero_resonant (support on {r_mu >= q+1})
% Lean @ d56efc8: Grammar/SmoothResolvedRLCTAsymptotic.lean: Grammar.SmoothEngine.ResolvedData.exists_rlct_asymptotic (Z_n[1] ~ c n^{-lam} (log n)^{m-1}, c>0)
% Lean @ d56efc8: Grammar/SmoothStratumMeasurePositive.lean: Grammar.SmoothEngine.ResolvedData.observableCoeff_pos_of_realised (positivity at the extremal pair)
% Lean: the chart shape of a general coefficient is the face construction defining smoothCoeff; no separate structure theorem is asserted.
\begin{thm}[The population expansion]\label{thm:population_expansion}
For smooth $f$ and $\varphi$ there is an asymptotic expansion
\[
\Zcal_n[f]\sim\sum_{\mu\in Q^{-1}\N}\ \sum_{q=0}^{d-1}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q,\qquad Q=2\prod_ik_i ,
\]
in the sense of \cref{sec:scale}, with the following properties. Each $c_{\mu,q}$ is a linear functional of $f$ which vanishes on every $f$ whose pull-back vanishes near the set of points through which at least $q+1$ walls resonate with $\mu$, a wall $E_i$ resonating when $2k_i\mu-h_i-1\in\N$; in particular $c_{\mu,q}=0$ unless some stratum all of whose walls resonate with $\mu$ has depth at least $q+1$. In a chart each coefficient is a finite sum of normal derivatives of the localised amplitude integrated over faces of the chart cube (\cref{app:chart_proofs}), of the shape \eqref{eq:conormal_presentation}. The exponents that occur are of the form $(h_i+\alpha+1)/2k_i$, $\alpha\in\N$. The first candidate contribution of a stratum $S_I$ is at $\lambda_I(f)$ with logarithmic degree $m_I(f)-1$, with $l_i$ the vanishing orders of \cref{sec:wallcrossing}; its face term is an integral over the stratum of the leading normal jet of $f$ against a positive density, and at the extremal pair, where the normal orders are zero and no other term competes, it is nonzero for $f\ge0$ positive somewhere on the stratum where the prior is positive. In particular
\[
\Zcal_n[1]\sim c\,n^{-\lambda}(\log n)^{m-1},\qquad c>0 ,
\]
with $(\lambda,m)$ the real log canonical threshold and its multiplicity of \cref{sec:stratification}.
\end{thm}

The theorem is proved for smooth data by an argument that never expands anything in a Taylor series in the tangential directions: in each chart the integral is reduced, by Fubini along the resonant normal directions, to one-dimensional integrals whose expansion is proved by scaling with an explicit remainder, and the remainder is estimated uniformly in the tangential variable. The argument is given in \cref{app:chart_proofs}, and it is the same argument that gives the empirical expansion of \cref{sec:empirical} once the field is put into the exponent. The rest of this section is about the coefficients.

\subsection{Depth, exact strata and admissible observables}\label{sec:exact_strata}

Fix an exponent $\mu$. At a point $P\in E$ of depth $c$, with normal directions labelled by the components through $P$, say that a wall $E_i$ \emph{resonates} with $\mu$ if $\alpha_i:=2k_i\mu-h_i-1\in\N$, and write $r_\mu(P)$ for the number of resonating walls through $P$. The \emph{exact stratum} at $(\mu,c)$ is
\[
S^\mu_c=\{P\in E:\ \operatorname{depth}(P)=c,\ r_\mu(P)=c\} ,
\]
the depth-$c$ points all of whose walls resonate; it is a union of strata $S_I$ with $|I|=c$, a locally closed submanifold of codimension $c$. Its closure lies in the closed set $D_c$ of \cref{sec:stratification} and its boundary in $D_{c+1}$, and on the open set $X_c=U\setminus D_{c+1}$ it is relatively closed. The coefficient $c_{\mu,q}$ is supported on the closed set $\{r_\mu\ge q+1\}$, a superlevel set of the resonance count rather than a stratum: a boundary point of the locus where $q+1$ walls resonate lies where more walls meet and belongs to the set automatically.

Call an observable \emph{admissible at depth $c$} if $f\circ\pi$ vanishes on a neighbourhood of $D_{c+1}$, and write $\Ical_{c+1}$ for the space of such pulled-back observables. The filtration $\Ical_1\subseteq\Ical_2\subseteq\cdots$ grades observables by how deep into the divisor they can see: an observable in $\Ical_{c+1}$ sees the strata of depth at most $c$ and is blind to the deeper crossings. Every statement about the depth-$c$ term below is made for admissible observables and on $X_c$. The reason is that at the boundary of an exact stratum a further wall arrives, the residue density of the stratum acquires a further pole, and it blows up whenever $\mu$ exceeds the exponent of the arriving wall; an admissible observable vanishes in a collar around that boundary, so the blow-up is met only where the observable is already zero. In \cref{ex:planes}, admissibility at depth one means vanishing near the axis, and admissibility at depth two is automatic since there are no points of depth three.

\input{figures/depth}

\subsection{The graded stratum formula}\label{sec:graded}

% Lean @ d56efc8: Grammar/SmoothResolvedStratumFormula.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_deep, Grammar.SmoothEngine.ResolvedData.coeff_eq_stratumSum
% Lean @ d56efc8: Grammar/SmoothFaceSumCollapse.lean: Grammar.SmoothEngine.smoothCoeff_eq_faceSum_top (chart form, JetsZeroOn the deep set)
% Lean @ d56efc8: Grammar/SmoothFaceMonoTop.lean: Grammar.SmoothEngine.faceMonoCoeff_top (constant Gamma(mu)/((c-1)! prod 2k_j); the 1/alpha_j! is faceW)
\begin{thm}[Graded stratum formula]\label{thm:graded}
Let $c\ge1$ and $f\circ\pi\in\Ical_{c+1}$. Then $c_{\mu,q}(f)=0$ for $q\ge c$, and $c_{\mu,c-1}(f)$ is a finite sum of absolutely convergent integrals over $S^\mu_c$. In a normal crossing chart with face coordinates $u_J=0$, $|J|=c$, the contribution of the face differentiates the whole localised amplitude $\eta=\rho\,g\,(f\circ\pi)$, the cutoff times the smooth density factor $g$ of \eqref{eq:real_normal_form} times the observable, in the $c$ normal directions to the resonant orders $\alpha_j=2k_j\mu-h_j-1$, integrates against the tangential weight, and multiplies by a constant; here $0_J$ is the point of the face with all $J$-coordinates zero and $w$ collects the remaining coordinates:
\begin{equation}\label{eq:graded}
\frac{\Gamma(\mu)}{(c-1)!\prod_{j\in J}2k_j\,\alpha_j!}\int_{u_J=0}\partial^\alpha_J\eta\,(0_J,w)\;\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,dw .
\end{equation}
Only faces all of whose walls resonate contribute, and a face point with exactly the $J$-coordinates zero is a point of depth $|J|$, so these are integrals over $S^\mu_c$.
\end{thm}

The theorem says that the top logarithmic power at an exponent sees only the deepest exact stratum: a face of smaller depth produces a pole of lower order and cannot reach $(\log n)^{c-1}$. The vanishing of the degrees $q\ge c$ is a separate statement of the same construction. The summed coefficient is the invariant object; it descends to the quotient of $\Ical_{c+1}$ by the observables vanishing near $D_c$, and the finer statement, that it depends only on a transverse jet along the exact stratum, is \cref{thm:jet}. The individual chart contributions are not asserted to be canonical, in accordance with \cref{sec:conormal}. The tangential weight $\prod_{i\notin J}w_i^{h_i-2k_i\mu}$ is integrable up to the boundary of the face exactly when $\mu<(h_i+1)/2k_i$ for every complementary wall $i$, resonant or not (for $K=x^2y^2$ at $\mu=1/2$ and $c=1$ the complementary wall is resonant and the weight $dx/|x|$ diverges); admissibility removes the need for this, since the amplitude vanishes near the deeper faces. Where the condition does hold, the formula is valid for all smooth $f$, which is the situation of \cref{sec:tiers}.

\subsection{Jet dependence, without coordinates}\label{sec:jets}

With the transverse jets of \cref{sec:conormal}, define, for $P\in E$, the \emph{intrinsic jet order}
\[
n_\mu(P)=\sum_{\text{walls }E_i\text{ through }P}\max\big(\lfloor2k_i\mu\rfloor-h_i-1,\,0\big) ,
\]
so that only walls whose resonant order is nonnegative count; at a point of $S^\mu_c$ every wall resonates and $n_\mu(P)=|\alpha|$.

% Lean @ d56efc8: Grammar/SmoothStratumJetDependence.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_of_memIdealPow, Grammar.SmoothEngine.ResolvedData.stratumJetOrder (= n_mu(P)), Grammar.SmoothEngine.ResolvedData.MemIdealPowNear
% Lean @ d56efc8: Grammar/SmoothStratumJetDescent.lean: Grammar.SmoothEngine.ResolvedData.descendedCoeff, Grammar.SmoothEngine.ResolvedData.admissible, Grammar.SmoothEngine.ResolvedData.jetKernelAdm
\begin{thm}[Jet dependence]\label{thm:jet}
Let $c\ge1$ and $F,F'\in\Ical_{c+1}$. If the germ of $F-F'$ at every $P\in S^\mu_c$ lies in $\Ical_{S^\mu_c,P}^{\,n_\mu(P)+1}$, then $c_{\mu,c-1}$ takes the same value on $F$ and $F'$. The functional therefore descends to the quotient of the admissible observables by those lying in $\Ical_{S^\mu_c}^{\,n_\mu(\cdot)+1}$ near every point of the stratum.
\end{thm}

The proof runs through \cref{thm:graded}: at an exactly resonant face the amplitude is a smooth multiple of $F$, a difference in $\Ical_S^{\,|\alpha|+1}$ is locally a sum of smooth multiples of products of $|\alpha|+1$ functions vanishing at the face, and a coordinate derivative of total order $|\alpha|$ of such a product vanishes there because the Leibniz rule leaves some factor undifferentiated. The order $n_\mu(P)$ is an upper bound: cancellations, or vanishing of the prior, can lower the true order at particular points. In the language of \cref{sec:conormal}, the coefficient depends on the observable only through its transverse $|\alpha|$-jet along the exact stratum. This is the precise form of the statement that the observable is seen through finitely many normal derivatives on a stratum, and it needs no choice of tubular neighbourhood.

\subsection{The stratum measure}\label{sec:stratum_measure}

Now impose the \emph{zero-order condition} on $S^\mu_c$: every wall through the exact stratum satisfies $2k_j\mu=h_j+1$, so that all $\alpha_j=0$ and the twisted density $(K\circ\pi)^{-\mu}\pi^*(\varphi\,dw)$ has simple poles along the $c$ walls. Then \cref{thm:graded} contains no derivatives, the functional $c_{\mu,c-1}$ is nonnegative on nonnegative admissible observables and depends only on their values on $S^\mu_c$, and a positive local linear functional is a measure.

% Lean @ d56efc8: Grammar/SmoothStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.stratumMeasure (def), Grammar.SmoothEngine.ResolvedData.coeff_withF_eq_integral_stratumMeasure, Grammar.SmoothEngine.ResolvedData.stratumMeasure_compl_exactStratum, Grammar.SmoothEngine.ResolvedData.eq_stratumMeasure_of_tests, Grammar.SmoothEngine.ResolvedData.stratumMeasure_eq_of_transports
% Lean @ d56efc8: Grammar/SmoothResolvedStratumPositive.lean: Grammar.SmoothEngine.ResolvedData.ZeroOrder, Grammar.SmoothEngine.ResolvedData.exactStratum
% Lean @ d56efc8: Grammar/SmoothStratumTest.lean: Grammar.SmoothEngine.ResolvedData.stratumOpen (= X_c), Grammar.SmoothEngine.ResolvedData.IsTest
\begin{thm}[The stratum measure]\label{thm:stratum_measure}
Let $c\ge1$ and assume the zero-order condition on $S^\mu_c$. There is a positive Radon measure $\nu^\mu_c$ on $X_c=U\setminus D_{c+1}$, carried by the exact stratum, such that for every $f$ with $f\circ\pi\in\Ical_{c+1}$ the restriction of $f\circ\pi$ to $X_c$ is $\nu^\mu_c$-integrable and
\begin{equation}\label{eq:stratum_measure}
c_{\mu,c-1}(f)=\int_{X_c}f\circ\pi\,d\nu^\mu_c .
\end{equation}
It is the unique positive Radon measure on $X_c$ with these integrals on smooth compactly supported tests, and for the fixed resolution and prior it does not depend on the tubular neighbourhoods, cutoffs or partitions of unity used to compute it.
\end{thm}

The construction is the Riesz--Markov--Kakutani theorem applied to $T[G]=c_{\mu,c-1}[G]$ on smooth compactly supported tests $G$ in $X_c$: $T$ is linear, positive and local to the stratum, and it satisfies the fixed-support bound $|T[G]|\le\|G\|_\infty T[\chi_L]$ for a cutoff $\chi_L$ equal to one on a compact $L$ containing the support of $G$, which gives continuity and hence extension to $C_c(X_c)$. Nothing is asserted about $\nu^\mu_c$ across $D_{c+1}$: it need not have finite mass, and it is not extended to $U$.

\subsection{The weighted logarithmic residue}\label{sec:residue}

The stratum measure has a name from complex geometry. Write $a=\rho\,g$ for the density amplitude without the observable, so that the localised amplitude of \cref{thm:graded} is $\eta=a\,(f\circ\pi)$. In a normal crossing chart the twisted density near a face $u_J=0$ of the exact stratum is
\[
\prod_{j\in J}|u_j|^{h_j-2k_j\mu}\,a(u)\,|du|=\prod_{j\in J}\frac{|du_j|}{|u_j|}\cdot a\,|du_{J^c}| ,
\]
with every pole simple under the zero-order condition. Extracting the pole along $E_j$ against $d\log(u_j^{2k_j})=2k_j\,du_j/u_j$ contributes a factor $(2k_j)^{-1}$, and doing so for all $j\in J$ leaves on the face the density
\begin{equation}\label{eq:face_density}
\prod_{j\in J}(2k_j)^{-1}\,a(0,w)\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,|dw| ,
\end{equation}
which is exactly the tangential weight of \eqref{eq:graded} at zero order, before the observable is inserted. Define
% Lean @ d56efc8: Grammar/SmoothStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.residueMeasure (def: ((c-1)!/Gamma(mu)) * stratumMeasure), Grammar.SmoothEngine.ResolvedData.residueMeasure_compl_exactStratum
\begin{equation}\label{eq:residue_measure}
\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c .
\end{equation}

% Lean @ d56efc8: Grammar/SmoothChartResidueMeasure.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure (def: face densities with (2k_j)^{-1} per wall)
% Lean @ d56efc8: Grammar/SmoothChartResidueIdentity.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure_eq_residueMeasure
\begin{thm}[The residue formula]\label{thm:residue}
Under the zero-order condition, for every admissible $f$ the integral $\int f\circ\pi\,d\Rres^\mu_c$ is the sum over charts and over simple faces $J$ of the face integrals of $f\circ\pi$ against \eqref{eq:face_density}, with chart and face multiplicities retained, and
\[
c_{\mu,c-1}(f)=\frac{\Gamma(\mu)}{(c-1)!}\int_{S^\mu_c}f\circ\pi\,d\Rres^\mu_c .
\]
\end{thm}

The measure $\Rres^\mu_c$ has two coordinate-free descriptions, and their agreement is what licenses the name.

\paragraph{Through the asymptotics.} Nothing in \eqref{eq:residue_measure} uses a chart: $\Rres^\mu_c$ is defined by coefficient extraction, and when no term more dominant than $n^{-\mu}(\log n)^{c-1}$ is present, which is the case at the leading pair and, for an admissible test, whenever all the more dominant candidate coefficients vanish, it is given by the limit
% Lean @ d56efc8: Grammar/SmoothStratumMeasureExtremal.lean: Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal (the limit in the leading situation)
% Lean: the sublevel-set form below is a derivation, not formalised.
\begin{equation}\label{eq:defA}
\int F\,d\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\lim_{n\to\infty}n^{\mu}(\log n)^{-(c-1)}\int_UF\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw)
\end{equation}
for $F$ vanishing near $D_{c+1}$; in general the more dominant terms must be subtracted first. $\Rres^\mu_c$ is the unique regular measure on $X_c$ with the coefficient values on tests. In the same leading situation one may replace the Laplace weight by sublevel sets of the phase,
\[
\int F\,d\Rres^\mu_c=\lim_{\delta\to0}\frac{c!}{(\log1/\delta)^c}\int_{\{K\circ\pi>\delta\}}F\,(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw) ,
\]
a truncated negative moment of the phase against the prior; in the logarithmic coordinates $t_j=2k_j\log(1/|u_j|)$ the region is the simplex $\sum t_j<\log(1/\delta)$, whose volume $(\log1/\delta)^c/c!$ is where the constant and the multiplicities $2k_j$ come from.

\paragraph{As an iterated density residue.} A positive density $\omega$ with a simple pole along a hypersurface $\{g=0\}$, meaning that $|g|\omega$ extends smoothly across it, has a residue $\operatorname{res}\omega=(|g|\omega)|_{\{g=0\}}/|dg|$, a positive density on the hypersurface independent of the choice of $g$, and characterised by the logarithmic divergence of the collar integral: $\int G\,\operatorname{res}\omega=\lim_{\varepsilon\to0}\frac1{2\log(1/\varepsilon)}\int_{\varepsilon<|g|<r}\tilde G\,\omega$ for a two-sided wall, with $\log(1/\varepsilon)$ in place of $2\log(1/\varepsilon)$ for a one-sided one. Along $c$ walls meeting transversally the residue is iterated, and for densities every step is unsigned and the result is symmetric in the walls. Summing over the permitted normal sides of each wall and dividing by the multiplicity $2k_j$ of the divisor of $K\circ\pi$,
\begin{equation}\label{eq:defB}
\Rres^\mu_c=\frac{2^{c_{\mathrm{int}}}}{\prod_{j\in J}2k_j}\,\operatorname{res}_{S^\mu_c}\big[(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw)\big]
\end{equation}
on each component of the stratum with walls $J$, where $c_{\mathrm{int}}$ is the number of interior (two-sided) walls among them and the density factor is assumed to match on the two sides; in general the residue measure is the sum over the permitted normal orthants of the one-sided residues, with $(2k_j)^{-1}$ per wall. Both the divisor and its multiplicities are intrinsic to $K\circ\pi$, so this is a coordinate-free density on the exact stratum.

% Lean @ d56efc8: Grammar/SmoothChartResidueIdentity.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure_eq_residueMeasure
% Lean: the manifold-level residue calculus for densities is not developed formally; the identity is with the chart face densities.
\begin{thm}[Identity of the two descriptions]\label{thm:identity}
Under the zero-order condition, the iterated density residue \eqref{eq:defB}, computed in any resolved chart atlas as the sum of the face densities \eqref{eq:face_density} pushed into $U$ and restricted to $X_c$, is a regular measure on $X_c$ that integrates tests to the residue sums of \cref{thm:residue}. Hence it equals $\Rres^\mu_c$, and $\nu^\mu_c=\frac{\Gamma(\mu)}{(c-1)!}\Rres^\mu_c$.
\end{thm}

The classical Poincar\'e residue takes a meromorphic form with a simple pole to a form on the polar hypersurface and is signed; here the object with the pole is a positive density and the residue is a positive density on the stratum. The two agree up to sign and normalisation where both make sense. The sanity check in one variable: for $K=x^{2k}$ on $\R$ with $\mu=1/2k$ and $\varphi\,dx=dx$, the residue of $|x|^{-1}|dx|$ at the origin is $1$, the two sides give $2$, and $\Rres^\mu_1=\frac1k\delta_0$, which is the coefficient of $n^{-1/2k}$ in $\int e^{-nx^{2k}}dx=\Gamma(\frac1{2k})n^{-1/2k}/k$ divided by $\Gamma(\mu)$.

\subsection{The leading term with insertion}\label{sec:leading}

Let $\lambda$ be the minimum of the wall exponents $(h_i+1)/2k_i$ over the components with real points and $m$ the maximum number of walls of exponent $\lambda$ through a point of $E$. Extremality forces the zero-order condition on every exact $\lambda$-resonant stratum, since a resonant wall with $2k\lambda=h+1+\alpha$, $\alpha\ge1$, would have exponent below $\lambda$. So the stratum measures $\nu^\lambda_c$ exist for every $c$, and the deepest one describes the leading term.

% Lean @ d56efc8: Grammar/SmoothStratumMeasureExtremal.lean: Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure (def), Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal
% Lean @ d56efc8: Grammar/SmoothStratumMeasurePositive.lean: Grammar.SmoothEngine.ResolvedData.observableCoeff_pos_of_realised
% Lean @ d56efc8: Grammar/SmoothStratumMeasureFinite.lean: Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure_univ_le, Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure_univ_eq_of_deep_empty
% Lean @ d56efc8: Grammar/SmoothResolvedRLCTIndex.lean: Grammar.SmoothEngine.ResolvedData.IsExtremalData
\begin{thm}[Leading asymptotic with insertion]\label{thm:leading}
For every smooth $f$ whose pull-back vanishes on a neighbourhood of $D_{m+1}$,
\[
n^{\lambda}(\log n)^{-(m-1)}\,\Zcal_n[f]\longrightarrow\int_Xf\circ\pi\,d\nu^\lambda_m=\frac{\Gamma(\lambda)}{(m-1)!}\int_{S^\lambda_m}f\circ\pi\,d\Rres^\lambda_m .
\]
If $f\ge0$ is positive at the image of a point of $S^\lambda_m$ at which the prior is positive, the limit is positive and $\Zcal_n[f]\sim\big(\int f\circ\pi\,d\nu^\lambda_m\big)n^{-\lambda}(\log n)^{m-1}$. The leading stratum measure is finite, with $\nu^\lambda_m(X)\le c_{\lambda,m-1}(1)$, and with equality when $D_{m+1}=\varnothing$.
\end{thm}

The admissibility hypothesis is vacuous when $D_{m+1}$ is empty, as in \cref{ex:planes}; in \cref{ex:mixed} the origin lies in $D_2$ while $m=1$. It is a restriction of the formal statement, not of the mathematics. At the extremal pair a further wall through a point of the closure of $S^\lambda_m$ has exponent strictly greater than $\lambda$, since equality would produce a point with $m+1$ walls of exponent $\lambda$; its tangential weight $w^{h-2k\lambda}$ therefore has exponent greater than $-1$ and is integrable, the leading residue density extends across $D_{m+1}$ with finite mass, giving $D_{m+1}$ measure zero though its closed support may meet it, as the bound $\nu^\lambda_m(X)\le c_{\lambda,m-1}(1)$ records, and the leading formula holds for every smooth $f$ with the extended measure (in \cref{ex:mixed} the weight $x^{-1/3}$ is integrable at the origin). This extension is a derivation and is not among the pinned declarations; wherever the normalised leading measure $\nu^\lambda_m/\nu^\lambda_m(X)$ is used below for the denominator $\Zcal_n[1]$, either $D_{m+1}=\varnothing$ or the extended measure is understood.

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample at a = 0 (x^2y^2 on the unit square, constant amplitude)
% Lean: the displayed measures for general prior are derivations from thm:residue.
\begin{example}[The running examples]\label{ex:population_examples}
For \cref{ex:planes} the components are the planes $E_1=\{x=0\}$, $E_2=\{y=0\}$ with $(k,h)=(1,0)$, $\lambda=1/2$, $m=2$, and $D_3=\varnothing$, so every observable is admissible at depth two. The twisted density is $\varphi\,dx\,dy\,dz/|xy|$, with simple poles along both planes. At depth two the exact stratum is the axis; each of the four quadrants around it contributes the iterated residue with a factor $1/2$ per wall, and
\[
\nu^{1/2}_2=\sqrt\pi\,\varphi(0,0,z)\,dz\quad\text{on the axis},\qquad \Zcal_n[f]\sim\sqrt\pi\Big(\int_{-1}^1f(0,0,z)\varphi(0,0,z)\,dz\Big)n^{-1/2}\log n\quad\text{when the axis average is nonzero}.
\]
The posterior concentrates on the axis with density proportional to the prior along it, and the leading expectation of $f$ is its prior-weighted average along the axis. At depth one the exact stratum is the two planes minus the axis, $X_1=U\setminus\{x=y=0\}$, and
\[
\nu^{1/2}_1=\sqrt\pi\Big(\varphi(x,0,z)\frac{dx\,dz}{|x|}+\varphi(0,y,z)\frac{dy\,dz}{|y|}\Big) ,
\]
with infinite mass near the axis. For $f$ vanishing near the axis, $c_{1/2,0}(f)=\int f\,d\nu^{1/2}_1$ is the coefficient of $n^{-1/2}$ without a logarithm. For $f$ not vanishing on the axis the $n^{-1/2}$ coefficient is not this divergent integral but a finite part in which the axis and the planes share the constant non-canonically. The complete functional $c_{1/2,0}$ is canonical, and its restriction to observables vanishing near the axis is the plane-measure integral; only its decomposition into plane finite parts and an axis term depends on conventions. For \cref{ex:mixed}, $\lambda=1/6$ with $m=1$, the exact stratum at $(1/6,1)$ is the line $\{y=0\}$ minus the origin, and since the wall $\{x=0\}$ has exponent $1/2>1/6$ the weight $x^{0}(x^{2})^{-1/6}=x^{-1/3}$ is integrable up to the origin: the leading measure is $\frac{\Gamma(1/6)}{6}\,\varphi(x,0)\,x^{-1/3}dx$ on $[0,1]$, finite, and no admissibility is needed.
\end{example}

\input{figures/x2y2}

\subsection{The Laurent data and the three tiers}\label{sec:tiers}

The stratum measures describe the top logarithmic coefficient at each exponent under the zero-order condition. All the coefficients are described at once by a single meromorphic function. For $0<\operatorname{Re}s<\lambda$ the Mellin transform of the partition function in $n$ is, by Fubini,
\begin{equation}\label{eq:zeta_global}
\mathcal Z_f(s)=\int_0^\infty n^{s-1}\Zcal_n[f]\,dn=\Gamma(s)\int_Wf\,K^{-s}\,\varphi\,dw=\Gamma(s)\int_U(f\circ\pi)\,(K\circ\pi)^{-s}\,\pi^*(\varphi\,dw) ,
\end{equation}
Watanabe's zeta function of the pair $(K,\varphi)$ with the observable inserted. It continues meromorphically to $\mathbb C$, with possible poles in $\operatorname{Re}s>0$ on the lattice and, from $\Gamma(s)$, at the nonpositive integers, and the expansion of \cref{thm:population_expansion} is equivalent to the statement
% Lean @ d56efc8: Grammar/MellinRegularization.lean: Grammar.mellin_eq_mellin_cutoffRemainderFun_add_principalParts
% Lean @ d56efc8: Grammar/PrincipalPartUniqueness.lean: Grammar.polarCoeff_unique, Grammar.mellinContinuation, Grammar.polarCoeff
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaPolar.lean: fluctuationZeta_eq_mellinContinuation, isFrozenCoeff_polarCoeff_unique (population case = zero field)
\begin{equation}\label{eq:laurent}
c_{\mu,q}(f)=\frac{(-1)^{q+1}}{q!}\,\big[(s-\mu)^{-(q+1)}\big]\,\mathcal Z_f(s) ,
\end{equation}
the coefficient of $n^{-\mu}(\log n)^q$ being the Laurent coefficient of order $q+1$ at $s=\mu$. Every coefficient is thus the pairing of the amplitude with a Laurent coefficient of the meromorphic distribution-valued function $s\mapsto(K\circ\pi)^{-s}\pi^*(\varphi\,dw)$, whose poles sit on the resonant strata. This is the definition from which the two closed forms below are evaluations, and it is the form in which the empirical coefficients of \cref{sec:empirical} will be obtained by replacing $\Gamma(s)$ with the fluctuation function.

\paragraph{One resonant coordinate.} Suppose that at $\mu$ only one wall $E_{i_0}$ resonates near the points in question, with $\alpha=2k_{i_0}\mu-h_{i_0}-1\in\N$. Then the pole of \eqref{eq:zeta_global} is simple, there is no logarithm, and in a chart with normal coordinate $u$ for $E_{i_0}$ and tangential coordinates $w$,
% Lean: not formalised; the closed finite-part form is a derivation; the formal coefficient at this pair is smoothCoeff (Taylor-subtracted face construction, Grammar/SmoothGeneral.lean), and for alpha <= 1 under the gap hypothesis it is empCoeff_generic at zero field (Grammar/FirstCorrection.lean).
\begin{equation}\label{eq:tier2}
c_{\mu,0}(f)=\frac{\Gamma(\mu)}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\eta\,(0,w)\;\prod_{i\ne i_0}w_i^{h_i}\Big(\prod_{i\ne i_0}w_i^{2k_i}\Big)^{-\mu}\,dw ,
\end{equation}
where $\eta$ is the localised amplitude and FP is the Hadamard finite part in those $w_i$ with $(h_i+1)/2k_i<\mu$: in one tangential variable with $a=h-2k\mu$ not a negative integer and $N$ large,
\[
\mathrm{FP}\!\int_0^1g(w)w^a\,dw=\int_0^1\Big(g(w)-\sum_{j\le N}\frac{g^{(j)}(0)}{j!}w^j\Big)w^a\,dw+\sum_{j\le N}\frac{g^{(j)}(0)}{j!\,(a+j+1)} ,
\]
the subtraction of the Taylor polynomial together with the compensating integrated monomials, iterated in the several variables and with the boundary cutoffs fixed; when $\mu$ is below every other exponent the integral converges and no finite part is needed. Up to the sign $(-1)^\alpha$ this is the pairing with $\delta^{(\alpha)}(u)\otimes\mathrm{FP}\,w^{h-2k\mu}$. In \cref{ex:mixed} the leading term is the case $\alpha=0$ and the first correction at $n^{-1/3}$ the case $\alpha=1$, both with convergent integrals since $1/3<1/2$:
\[
c_{1/3,0}(f)=\frac{\Gamma(1/3)}{6}\int_0^1\partial_y\eta(x,0)\,x^{-2/3}\,dx,\qquad \eta=\varphi\cdot f .
\]

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (x^2y^2, constant amplitude: n^{-1/2}/4 [Gamma(1/2) log n - Gamma'(1/2)] at a = 0)
% Lean: the x^2y^2 formulas for nonconstant amplitude are derivations.
\paragraph{Ties.} When $c$ walls resonate at $\mu$ the pole has order $c$. The coefficient of the top power $(\log n)^{c-1}$ is the graded formula \eqref{eq:graded}, a product of normal deltas against the residue density on the face. The lower powers are read off the Laurent expansion: Taylor-expanding the amplitude in the coordinates $u_J$ to order $\alpha$ and integrating $u_J^{h_J+\alpha-2k_Js}$ over the $J$-cube produces the factor $\prod_{j\in J}(2k_j(\mu-s))^{-1}$ times the tangential integral of $\partial^\alpha_J\eta(0_J,w)/\alpha!$ against $w^{h-2ks}$; expanding that tangential integral around $s=\mu$ contributes the powers of $\log w^{2k}$, and the expansion of $\Gamma(s)$ contributes derivatives of the Gamma function. A face $J'\supsetneq J$ resonating at the same $\mu$ makes the tangential integral itself singular, raising the pole order, and its finite part is what the lower coefficients compute. In the simplest tie, \cref{ex:planes} at $\mu=1/2$ with amplitude $\eta=\varphi f$ restricted to a slice $z=$ const, one finds, with $\eta_s=\Gamma(s)\eta$,
\[
c_{1/2,1}=\frac{\eta_{1/2}(0,0)}4,\qquad c_{1/2,0}=-\frac{\partial_s\eta_s(0,0)|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}{x}\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}{y}\,dy
\]
per quadrant and per $z$, each quadrant with its own pulled-back amplitude; the full coefficients are obtained by summing the four quadrants and integrating over $z$. The lower logarithm at a tie is the derivative in the exponent at the deepest stratum plus finite parts of the amplitude along the subfaces. The derivative in the exponent, here $\Gamma'(1/2)\eta(0,0)$, becomes in the empirical case the index derivative of the fluctuation function.

\subsection{Population posterior expectations}\label{sec:population_posterior}

The expectation $\E_\infty[f]=\Zcal_n[f]/\Zcal_n[1]$ is the quotient of two expansions in the same scale, and the leading block of the denominator has top term $c\,(\log n)^{m-1}$ with $c>0$, so the quotient is an expansion in the sense of \cref{sec:scale} with coefficients rational in $\log n$ (\cref{app:expansion_algebra}). Three cases arise at leading order, according to how $f$ meets the leading strata.

\begin{itemize}
% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO' (quotient of two cutoff expansions)
% Lean @ d56efc8: Grammar/MomentKernel.lean: HasLeadingTerm.div (ratio of leading terms)
\item \emph{Generic observable.} If $\int f\circ\pi\,d\nu^\lambda_m\ne0$, which holds when $f\circ\pi$ does not vanish identically on $S^\lambda_m$ and has a sign there, the exponents and logarithmic degrees of numerator and denominator agree and
\[
\E_\infty[f]\longrightarrow\frac{\int f\circ\pi\,d\nu^\lambda_m}{\nu^\lambda_m(X)} ,
\]
the average of $f$ against the normalised leading stratum measure. The posterior concentrates on the deepest exact strata of lowest exponent, with the density \eqref{eq:face_density}.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on all of $S^\lambda_m$ and $m'-1<m-1$ is the largest logarithmic degree at which its coefficient at $\lambda$ is nonzero, the exponent is unchanged and the logarithmic degree drops: $\E_\infty[f]\sim D(\log n)^{-(m-m')}$, $D\ne0$ (the largest degree matters: for $K=x^2y^2z^2$ on $[0,1]^3$ and $f=x^2$ the numerator has nonzero coefficients at degrees $1$ and $0$, and the rate is $2/\log n$). This is \cref{ex:planes} with $f=x^2$: the expectation decays like $1/\log n$, the rate at which the posterior concentrates on the axis.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$, the first candidate exponent of $\Zcal_n[f]$ is strictly larger and, if some coefficient of $\Zcal_n[f]$ is nonzero, $\E_\infty[f]=Dn^{-(\mu-\lambda)}(\log n)^{q-(m-1)}+o(\cdot)$ decays as a power, with $(\mu,q)$ the first such pair; an observable flat along the walls, such as $e^{-1/x^2}$ for $K=x^2$, has no nonzero coefficient and its expectation decays faster than every power. The observable $f=K$ is the canonical instance: $K\circ\pi$ vanishes to order $2k_i$ along every wall, shifting every exponent by exactly one, so $\E_\infty[K]\sim\lambda/n$, and indeed $\E_\infty[K]=-\frac{d}{dn}\log\Zcal_n[1]=\frac\lambda n-\frac{m-1}{n\log n}+\cdots$ exactly.
\end{itemize}

\input{figures/wall_crossing}

As the observable varies in a family, the vanishing orders along the walls are generically constant and change only at special values, where the candidate exponent of $\E_\infty[f_\tau]$ jumps by a rational amount determined by $(k_i,h_i,l_i)$; the actual exponent follows when the corresponding coefficient is nonzero. This wall-crossing is the discrete signal by which expectation values report the structure of $W_0$. In the running examples: for \cref{ex:planes}, $\E_\infty[f]\to\int f(0,0,z)\varphi(0,0,z)dz/\int\varphi(0,0,z)dz$ for $f$ with nonzero axis average and $\E_\infty[x^2]\sim C/\log n$; for \cref{ex:mixed}, $\E_\infty[f]\to\int_0^1f(x,0)\varphi(x,0)x^{-1/3}dx/\int_0^1\varphi(x,0)x^{-1/3}dx$. The full expansion of the quotient, to all orders, is deferred to \cref{sec:posterior}, where it is treated together with its empirical counterpart.
```

## sections/08_fluctuation.tex
```latex
\section{The fluctuation function}\label{sec:fluctuation}

The population expansion is built from one-variable integrals $\int u^he^{-nu^{2k}}du$, whose value is a Gamma function times a power of $n$. When the sample enters, the exponent acquires the term $\sqrt n\,u^k\zeta(u)$ of \cref{sec:setting}, and the same one-variable integral produces a different special function. This section introduces it, records the algebra it satisfies, and explains why that algebra is the whole mechanism by which the data enters the coefficients.

\subsection{The one-variable computation}

Take a single normal coordinate with data $(k,h)$ and freeze the field at a constant $a$. The substitution $t=nu^{2k}$ gives
\begin{equation}\label{eq:one_variable_field}
\int_0^\infty u^h\,e^{-nu^{2k}+\sqrt n\,u^ka}\,du=\frac{n^{-\mu}}{2k}\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}\,dt,\qquad \mu=\frac{h+1}{2k} ,
\end{equation}
because $\sqrt n\,u^k=\sqrt t$. The exponent is unchanged from the population case; the constant $\Gamma(\mu)$ has become a function of $a$.

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.fluctuation (def; general beta, here beta = 1)
\begin{defn}[Fluctuation function]\label{def:fluctuation}
For $\mu>0$ and $a\in\R$,
\begin{equation}\label{eq:fluctuation}
S_\mu(a)=\int_0^\infty t^{\mu-1}\,e^{-t+a\sqrt t}\,dt .
\end{equation}
\end{defn}

The integral converges for every $a$, since $-t+a\sqrt t=-(\sqrt t-a/2)^2+a^2/4$, and $S_\mu(0)=\Gamma(\mu)$. The same integral defines $S_s(a)$ for complex $s$ with $\operatorname{Re}s>0$, holomorphic in $s$, which is the form used in \cref{sec:empirical}. This is Watanabe's fluctuation function \citep[Def.~5.8]{watanabeAlgebraicGeometryStatistical2009} at unit temperature; a temperature $\beta$ is absorbed by $n\mapsto\beta n$ and $a\mapsto\sqrt\beta\,a$. Its probabilistic meaning is immediate from \eqref{eq:fluctuation}: $S_\mu(a)/\Gamma(\mu)=\E\,e^{a\sqrt T}$ for $T\sim\operatorname{Gamma}(\mu,1)$, the moment generating function of $\sqrt T$. The radial variable $t=nu^{2k}$ is the loss measured in units of $1/n$, its law under the population Gibbs weight is $\operatorname{Gamma}(\mu,1)$, and the sample tilts that law by $e^{a\sqrt t}$.

\subsection{The ladder}

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.deriv_fluctuation (i), Grammar.fluctuation_recurrence (ii), Grammar.fluctuation_ode (iii), Grammar.fluctuation_one (iv)
% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_iteratedDeriv (S_{(n+1)/2} = d^n S_{1/2}, regular orbit), fluctuation_half_gaussian ((v) as a Gaussian integral, before the erf normalisation)
% Lean: the erf normalisation in (v) and the Weber form eq:weber are analytic derivations.
\begin{lem}\label{lem:ladder}
For $\mu>0$: (i) $\partial_aS_\mu=S_{\mu+1/2}$; (ii) $S_{\mu+1}(a)=\frac a2S_{\mu+1/2}(a)+\mu S_\mu(a)$; (iii) $S_\mu''=\frac a2S_\mu'+\mu S_\mu$; (iv) $S_1(a)=\frac a2S_{1/2}(a)+1$; (v) $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}\big(1+\operatorname{erf}(a/2)\big)$.
\end{lem}

\begin{proof}
(i) is differentiation under the integral, since $\partial_ae^{a\sqrt t}=\sqrt t\,e^{a\sqrt t}$ raises the power of $t$ by one half. (ii) follows from $\int_0^\infty\frac{d}{dt}\big[t^\mu e^{-t+a\sqrt t}\big]dt=0$, whose integrand is $(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$; (iii) is (ii) rewritten with (i); (iv) is the same computation at $\mu=0$ on $[\varepsilon,T]$ with $\varepsilon\to0$; (v) is the substitution $u=\sqrt t$ and completion of the square.
\end{proof}

Property (i) is the \emph{ladder}: differentiating in the field variable raises the index by one half. Property (iii) is Weber's equation in disguise: under $S_\mu(a)=e^{a^2/8}f(a/\sqrt2)$ it becomes $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $-2\mu$, so that
% Lean: not formalised; Weber substitution and parabolic-cylinder closed form.
\begin{equation}\label{eq:weber}
S_\mu(a)=2^{1-\mu}\Gamma(2\mu)\,e^{a^2/8}\,D_{-2\mu}\big(-a/\sqrt2\big)
\end{equation}
in terms of the standard parabolic cylinder function \citep[\S12.5]{NIST:DLMF}. The operators $b^\dagger=\partial_a$ and $b=2\partial_a-a$ satisfy $[b,b^\dagger]=1$, the defining relation of the Weyl algebra, and act on the fluctuation functions by raising and lowering the index: $b^\dagger S_\mu=S_{\mu+1/2}$ and $bS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>1/2$, the recurrence (ii) being the statement that $b$ lowers. The space $\mathbb C[a]+\operatorname{span}\{S_{(n+1)/2}:n\ge0\}$ is stable under $b$ and $b^\dagger$, and the orbit of $\mu=1/2$, which is the regular case, is distinguished: there $S_{(n+1)/2}=\partial_a^nS_{1/2}$, so every fluctuation function of half-integer index is a derivative of $\sqrt\pi e^{a^2/4}(1+\operatorname{erf}(a/2))$, and modulo the polynomial submodule $S_{1/2}$ is a lowest-weight vector, a vector killed by $b$, from which $b^\dagger$ generates the whole orbit: this is the Fock representation of the Weyl algebra, in which $b^\dagger$ creates and $b$ annihilates. For a singular model with $\mu\notin\frac12\mathbb Z$ there is no lowest weight and the parabolic cylinder function is genuinely needed; the module structure is recorded in \cref{app:fluctuation_facts}. The same recurrence underlies Watanabe's equations of state for the Bayes and Gibbs errors \citep[Thm~5.11]{watanabeAlgebraicGeometryStatistical2009}; we will not need them.

The structural consequence for the expansions is this. Wherever the population theory produces a Gamma function $\Gamma(\mu)$ from a normal integral, the empirical theory produces $S_\mu$ evaluated on the field. Wherever the population theory differentiates the amplitude in a normal direction, the empirical theory also differentiates the factor $e^{\sqrt n u^k\zeta}$, and by the chain rule and \cref{lem:ladder}(i) every derivative of the field brings $S_{\mu+1/2}$, $S_{\mu+1}$, and so on. The corrections therefore involve a finite ladder of fluctuation functions of increasing index multiplied by derivatives of the field, in a pattern fixed by the Leibniz rule. In one variable it reads
% Lean @ d56efc8: Grammar/EmpiricalOneDim.lean: Grammar.SmoothEngine.empOneDimCoeff (def: d^j[eta S_{mu_j}(xi)](0)/(j! 2k)), Grammar.SmoothEngine.empOneDim_expansion, Grammar.SmoothEngine.empOneDimCoeff_one
\begin{equation}\label{eq:one_dim_coefficients}
\int_0^1\eta(u)u^he^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}du\sim\sum_{j\ge0}\frac{\partial_u^j\big[\eta\,S_{\mu_j}(\zeta)\big](0)}{j!\,2k}\,n^{-\mu_j},\qquad\mu_j=\frac{h+j+1}{2k} ,
\end{equation}
so that the $j$-th coefficient is the $j$-th derivative at the origin of the amplitude times the fluctuation function of the field at the $j$-th index: $\eta S_{\mu_0}(\zeta)/2k$, then $(\eta'S_{\mu_1}(\zeta)+\eta\zeta'S_{\mu_1+1/2}(\zeta))/2k$, then $(\eta''S_{\mu_2}+2\eta'\zeta'S_{\mu_2+1/2}+\eta\zeta''S_{\mu_2+1/2}+\eta\zeta'^2S_{\mu_2+1})/(2\cdot2k)$, and so on. This is the one-dimensional form of everything in \cref{sec:empirical}, and it is proved in \cref{app:chart_proofs} by scaling $u=n^{-1/2k}x$ and Taylor-expanding the smooth factor $\eta(u)e^{x^k\zeta(u)}$ in $u$ to finite order with a remainder.

\subsection{Index derivatives and logarithms}

The logarithms of the population expansion arise, in the Mellin picture, from higher-order poles, and in the coefficients they appear as derivatives of $\Gamma$ with respect to its argument. In the empirical theory they are derivatives of $S$ with respect to the index:
% Lean @ d56efc8: Grammar/MellinLogWeights.lean: Grammar.SmoothEngine.mellinMom_pow_mul_exp_eq_iteratedDeriv (log weights as index derivatives)
% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (the x^2y^2 display below)
\begin{equation}\label{eq:index_derivative}
\partial_\nu^\ell S_\nu(a)=\int_0^\infty t^{\nu-1}(\log t)^\ell\,e^{-t+a\sqrt t}\,dt ,
\end{equation}
by differentiation under the integral, which is legitimate for $\nu>0$. A term $(c-\log t)^p$ in a radial integral thus becomes the operator $(c-\partial_\nu)^p$ applied to $S_\nu$, and $\sum_p\frac{z^p}{p!}(c-\partial_\nu)^pS_\nu=e^{zc}S_{\nu-z}$ is the translation in the index. In the smallest example with a logarithm, $K=x^2y^2$ with a constant field $a$ on the unit square, the radial density of $u=xy$ is $-\log u$ and
\[
\int_0^1\!\!\int_0^1e^{-nx^2y^2+a\sqrt n\,xy}\,dx\,dy=\frac1{4\sqrt n}\int_0^n t^{-1/2}e^{-t+a\sqrt t}(\log n-\log t)\,dt=\frac{n^{-1/2}}4\Big[S_{1/2}(a)\log n-\partial_\nu S_\nu(a)\big|_{1/2}\Big]+o(n^{-1/2}) ,
\]
which at $a=0$ is $\frac{n^{-1/2}}4[\Gamma(\tfrac12)\log n-\Gamma'(\tfrac12)]$. The coefficient below the top power of the logarithm is an index derivative of the fluctuation function, and this is the general pattern: the lower logarithmic orders at a tied exponent carry $\partial_\nu^\ell S_\nu(\zeta)$, and the passage from the population to the empirical theory replaces $\Gamma^{(\ell)}(\mu)$ by $\partial_\nu^\ell S_\nu(\zeta)|_{\nu=\mu}$ throughout. The higher index derivatives satisfy an inhomogeneous Weber equation obtained by differentiating (iii) in $\mu$, a triangular system that determines them recursively.

\subsection{The field in the exponent, and the incomplete function}

In the actual integrals the radial variable runs over a bounded range, $t\le nb^{2k}$, and the fluctuation function is replaced by its incomplete version $S_\mu(a;T)=\int_0^Tt^{\mu-1}e^{-t+a\sqrt t}dt$, which satisfies the same ladder in $a$ and the same index-derivative identity, and an inhomogeneous Weber equation whose right side $-T^\mu e^{-T+a\sqrt T}$ is exponentially small in $T=nb^{2k}$. Replacing the incomplete function by the complete one therefore costs $O(e^{-\varepsilon n})$, invisible in the scale, exactly as the localisation to a neighbourhood of the divisor did in the population case. The field itself is not constant, and the way its variation enters is through the normal derivatives in \eqref{eq:one_dim_coefficients}; what is constant is the structure, the finite ladder of indices and the Leibniz pattern of derivatives, and the next section makes it the statement of a theorem in every dimension.
```

## sections/09_empirical.tex
```latex
\section{The empirical expansion for a fixed sample}\label{sec:empirical}

We distinguish three objects. The \emph{frozen} partition function $Z_N(\eta;\zeta)$ is a deterministic integral with a fixed smooth field $\zeta$ in the exponent and an independent parameter $N\to\infty$; it is of the same kind as the population one, and everything in Part~II goes through with one substitution: the Gamma function in the stratum measures becomes the fluctuation function of the field along the stratum, and derivatives of the field enter the corrections through the ladder. The \emph{empirical diagonal} $Z_n(\eta;\hat\psi_n)$ is the frozen partition function evaluated at $N=n$ and at the chart representative $\hat\psi_n$ of the sample's own field, defined below, which itself depends on $n$; statements about it are obtained from the frozen theorem through the uniformity of its remainder in the field. The \emph{limit} is the same coefficient functional evaluated on the Gaussian field $G$, in \cref{sec:limit}. This section is about the first object, and states what carries over to the second.

\subsection{Root fields}

Pulling the standard form \eqref{eq:standard_form} back along the resolution, on a chart where $K\circ\pi=u^{2k}$ we have $\sqrt{K\circ\pi}=|u^k|$ and
\begin{equation}\label{eq:exponent_chart}
-nK_n\circ\pi=-nu^{2k}+\sqrt n\,|u^k|\,(\psi_n\circ\pi) .
\end{equation}
The standard form supplies a smooth signed-root representative $\xi_n$ with $K_n\circ\pi=u^{2k}-n^{-1/2}u^k\xi_n$ \citep[Main Theorem~6.1]{greybook}; the function multiplying $|u^k|$ in \eqref{eq:exponent_chart} is $\operatorname{sgn}(u^k)\xi_n$, smooth on each orthant of the normal coordinates and in general discontinuous across an interior wall. The natural object is therefore a \emph{root field}: a bounded measurable function $\psi$ on $U$ together with, for every chart and every orthant of its normal coordinates, a smooth representative $\hat\psi$ on the closed box, agreeing with $\psi$ off the walls. Off the walls the representatives are determined; on the walls they record the one-sided limits, which need not agree, and it is the representatives that the coefficients see. Writing $\zeta=\hat\psi$ for the chart representative, the chart integral of $Z_n[f]$ is
\begin{equation}\label{eq:empirical_chart}
Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du ,
\end{equation}
with $\eta$ the localised amplitude of \cref{sec:population} and both $\eta$ and $\zeta$ smooth on the closed cube. Summing the chart integrals of a root field $\psi$ over the charts and orthants with the partition of unity of \cref{sec:population} gives the resolved frozen partition function, written $Z_N[f;\psi]$. For an analytic model $\zeta$ is analytic for each finite $n$; nothing below uses this.

\subsection{The expansion}

% Lean @ d56efc8: Grammar/EmpiricalGeneral.lean: Grammar.SmoothEngine.empIntegral (def), Grammar.SmoothEngine.emp_cutoffExpansion, Grammar.SmoothEngine.empCoeff_unique
% Lean @ d56efc8: Grammar/EmpiricalUniform.lean: Grammar.SmoothEngine.emp_cutoffExpansion_uniform (remainder linear in the FieldJetBound constant)
% Lean @ d56efc8: Grammar/EmpiricalFieldFamilyJets.lean: Grammar.SmoothEngine.FieldJetBound
% Lean @ d56efc8: Grammar/EmpiricalResolvedExpansion.lean: Grammar.SmoothEngine.ResolvedData.SmoothRootField (structure), Grammar.SmoothEngine.ResolvedData.SmoothRootField.empZ_cutoffExpansion, Grammar.SmoothEngine.ResolvedData.SmoothRootField.resolvedCoeff_zero
\begin{thm}[The empirical expansion, fixed sample]\label{thm:empirical_expansion}
Let $\eta,\zeta$ be smooth on a neighbourhood of the closed cube. Then $Z_N(\eta;\zeta)$ has a cutoff expansion in $N$ in the sense of \cref{sec:scale},
\[
Z_N(\eta;\zeta)\sim\sum_{\mu\in Q^{-1}\N}\sum_{q=0}^{d-1}c_{\mu,q}(\eta;\zeta)\,N^{-\mu}(\log N)^q ,
\]
with coefficients independent of the cutoff, and with a remainder constant at cutoff $U$ that is linear in a bound on the normal jets of $\eta\,e^{\tau\zeta}$ up to an order $R(U)$ on the closed cube, with the bound on $\zeta$ fixed. Assembled over the charts of the resolution with the partition of unity of \cref{sec:population}, the empirical partition function of a bounded smooth root field has a cutoff expansion on the common lattice with logarithmic degree at most $d-1$, whose coefficients at zero field are the population coefficients.
\end{thm}

The proof is the proof of \cref{thm:population_expansion} with the field carried along: Fubini along the resonant normal coordinates, the one-dimensional expansion \eqref{eq:one_dim_coefficients} with an explicit constant depending on the slice only through a bound on $\zeta$ and bounds on the normal jets of $\eta e^{\tau\zeta}$, and dominated convergence in the tangential variables (\cref{app:chart_proofs}). The uniformity in the jets is what allows the sample to vary: on the empirical diagonal $N=n$, $\zeta=\hat\psi_n$, the remainder at cutoff $U$ is bounded by the jet bound of the sample's field times $n^{-U}(1+\log n)^{d-1}$, so it is $O_P(n^{-U}(\log n)^{d-1})$ as soon as the jet bounds of the fields are tight, which is the form the statement takes in \cref{sec:limit}.

\subsection{The coefficients}

Three descriptions, each the empirical form of one in \cref{sec:population}.

\paragraph{Geometric: the top logarithmic order.} For an observable admissible at depth $c$, the coefficient of $n^{-\mu}(\log n)^{c-1}$ is the graded formula \eqref{eq:graded} with the amplitude $\eta$ replaced by $\eta\,S_\mu(\zeta)/\Gamma(\mu)$:
% Lean @ d56efc8: Grammar/EmpiricalFaceSumCollapse.lean: Grammar.SmoothEngine.empCoeff_eq_zero_of_deep, Grammar.SmoothEngine.empCoeff_eq_faceSum_top, Grammar.SmoothEngine.empCoeff_top_eq_smoothCoeff
% Lean @ d56efc8: Grammar/EmpiricalResolvedStratumFormula.lean: Grammar.SmoothEngine.ResolvedData.SmoothRootField.resolvedCoeff_eq_empStratumSum
\begin{equation}\label{eq:empirical_graded}
c_{\mu,c-1}(\eta;\zeta)=\sum_{|J|=c}\frac{\prod_{j\in J}(2k_j)^{-1}}{(c-1)!\prod_{j\in J}\alpha_j!}\int_{u_J=0}\partial^\alpha_J\big[\eta\,S_\mu(\zeta)\big](0_J,w)\;w^{h}\big(w^{2k}\big)^{-\mu}\,dw .
\end{equation}
In resolved form: the normal jet of order $\alpha$ of $(f\circ\pi)\,S_\mu(\hat\psi)$ along the exact stratum $S^\mu_c$, integrated against the chart residue data of \cref{sec:residue}, which at zero order is the weighted logarithmic residue $\Rres^\mu_c$ and at positive orders is the differentiated face density of \eqref{eq:graded}; the sum is over the orthants, each with its own representative $\hat\psi$. The geometry is that of the population expansion; the sample enters as a pointwise reweighting of the residue density by the fluctuation function of the standardised field, together with its normal derivatives, which raise the index by halves. At the leading pair $(\lambda,m)$, for $f$ admissible at depth $m$,
% Lean @ d56efc8: Grammar/EmpiricalResolvedLeading.lean: Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ, Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ_eq_integral
% Lean @ d56efc8: Grammar/EmpiricalStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.RootField (structure), Grammar.SmoothEngine.ResolvedData.empiricalStratumMeasure
\begin{equation}\label{eq:empirical_leading}
N^{\lambda}(\log N)^{-(m-1)}Z_N[f;\psi]\longrightarrow\frac1{(m-1)!}\sum_{\text{orthants}}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi)\,d\Rres^{\lambda,\pm}_m ,
\end{equation}
where $\Rres^{\lambda,\pm}_m$ are the one-sided residue densities whose sum is $\Rres^\lambda_m$; when the representatives agree on the two sides of every wall this collapses to $\frac1{(m-1)!}\int(f\circ\pi)S_\lambda(\hat\psi)\,d\Rres^\lambda_m$, and at $\psi=0$ it is \cref{thm:leading}. The leading empirical coefficient depends on the field only through its values on the leading stratum: the posterior at leading order lives on the deepest exact stratum and is the population stratum measure reweighted, orthant by orthant, by $S_\lambda(\hat\psi)$. And the reweighting is by a positive function, so the positivity and finiteness statements of \cref{thm:leading} survive, with $S_\lambda(\hat\psi)\le S_\lambda(\|\psi\|_\infty)$ giving domination by a multiple of the population measure.

\paragraph{Analytic: the fluctuation zeta function.} The Mellin transform of the frozen partition function in $n$ is, by \eqref{eq:one_variable_field} applied pointwise,
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZeta.lean: mellin_frozenEvidenceObs_eq
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaPolar.lean: fluctuationZeta_eq_mellinContinuation, isFrozenCoeff_polarCoeff_unique
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaStrip.lean: mellin_frozenEvidenceObs_eq_of_bounded_std, fluctuationZeta_eq_mellinContinuation_of_bounded_std, isFrozenCoeff_polarCoeff_unique_of_bounded (strip hypotheses derived)
% Lean @ d56efc8: Grammar/MellinRegularization.lean: Grammar.mellin_eq_mellin_cutoffRemainderFun_add_principalParts
% Lean @ d56efc8: Grammar/PrincipalPartUniqueness.lean: Grammar.polarCoeff_unique
\begin{equation}\label{eq:fluctuation_zeta}
\mathcal Z_f(s;\psi)=\int_0^\infty N^{s-1}Z_N[f;\psi]\,dN=\sum_{\text{orthants}}\int_U(f\circ\pi)\,(K\circ\pi)^{-s}\,S_s(\hat\psi)\,\pi^*(\varphi\,dw) ,
\end{equation}
Watanabe's zeta function with the Gamma factor replaced, inside the integral, by the fluctuation function of the standardised field at a complex index; the integral is written upstairs and branchwise because the field is a root field, with one representative per orthant, and not a function on $W$. Every coefficient of \cref{thm:empirical_expansion}, at every logarithmic order, is a Laurent coefficient of this function at a pole in $\operatorname{Re}s>0$, exactly as in \eqref{eq:laurent} (the possible poles of $S_s$ at $0,-\tfrac12,-1,\dots$ record the small-$N$ behaviour): $c_{\mu,q}=\frac{(-1)^{q+1}}{q!}[(s-\mu)^{-(q+1)}]\mathcal Z_f(s;\psi)$. This is the definition from which the geometric formula is an evaluation, and it is the description that covers the lower logarithmic orders at ties, where no closed geometric formula of the form \eqref{eq:empirical_graded} exists: there the index derivatives $\partial_\nu^\ell S_\nu(\zeta)$ of \cref{sec:fluctuation} carry the logarithms, in Taylor-subtracted chart expressions.

\paragraph{Algebraic: the generating identity.} Every empirical coefficient is a convergent series of population coefficients with powers of the field inserted into the observable:
% Lean @ d56efc8: Grammar/EmpiricalGeneratingIdentity.lean: Grammar.SmoothEngine.hasSum_empCoeff_population
\begin{equation}\label{eq:generating}
c_{\mu,q}(\eta;\zeta)=\sum_{r\ge0}\frac1{r!}\,c^{\mathrm{pop}}_{\mu+r/2,\,q}\big(\eta\,(u^k\zeta)^r\big) ,
\end{equation}
unconditionally convergent. The half-integer shift of the exponent is the bookkeeping for the $\sqrt n$ in front of the field: in the radial variable $t=nu^{2k}$ the term $(\sqrt t\,\zeta)^r/r!$ of the exponential is the insertion $(u^k\zeta)^r$ against the Gamma law at index $\mu+r/2$, and $S_\mu(a)=\sum_ra^r\Gamma(\mu+r/2)/r!$ is the same identity at a single point. The proof is by truncation of the exponential and never exchanges the series with the integral, and each term depends on the field only through its jet of a fixed order determined by $(h,k,\mu)$. The identity says that the population theory determines the empirical one: the sample enters through the population coefficients of the modified observables $f\,H^r$, $H=\sqrt K\,\psi$, with the exponent climbing by halves.

\subsection{What enters at the first orders}\label{sec:first_orders}

The abstract descriptions become concrete in the two situations of \cref{sec:tiers}.

\paragraph{One resonant coordinate.} If at $\mu$ only the wall $E_{i_0}$ resonates, with normal order $\alpha$, then, writing $u$ for the normal coordinate of $E_{i_0}$, $w$ for the remaining coordinates, $w^{h_L}=\prod_{i\ne i_0}w_i^{h_i}$ and $p(w)=w^{2k_L}=\prod_{i\ne i_0}w_i^{2k_i}$ as in \cref{app:chart_proofs},
% Lean: not formalised; closed finite-part form for alpha >= 2 past another wall's exponent; see sec:formalisation, first bullet.
\begin{equation}\label{eq:empirical_tier2}
c_{\mu,0}(\eta;\zeta)=\frac{1}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\big[\eta\,S_\mu(\zeta)\big](0,w)\;w^{h_L}\big(w^{2k_L}\big)^{-\mu}\,dw ,
\end{equation}
with the finite part needed only past the exponents of the other walls. Under the generic hypothesis that $\mu_1=\lambda+1/2k_{i_0}$ is below every other exponent, the two leading coefficients are plain integrals over the face, valid for all smooth $\eta,\zeta$ with no admissibility hypothesis:
% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.genericFaceCoeff (def), Grammar.SmoothEngine.empCoeff_generic, Grammar.SmoothEngine.empCoeff_firstCorrection, Grammar.SmoothEngine.tendsto_firstCorrection
\begin{align}
c_{\lambda,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\lambda}\,\eta(0,w)\,S_\lambda\big(\zeta(0,w)\big)\,dw,\label{eq:c_lambda}\\
c_{\mu_1,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\mu_1}\Big[\partial_u\eta(0,w)\,S_{\mu_1}\big(\zeta(0,w)\big)+\eta(0,w)\,\partial_u\zeta(0,w)\,S_{\mu_1+1/2}\big(\zeta(0,w)\big)\Big]dw,\label{eq:c_mu1}
\end{align}
and every other coefficient at a lattice exponent $\le\mu_1$ vanishes. The first correction is the one-dimensional coefficient $C_1$ of \eqref{eq:one_dim_coefficients} for the slice $(\eta(\cdot,w),\zeta(\cdot,w))$, integrated over the face against the residue density. Only the values and first normal derivatives of the amplitude and of the field on the face enter; the field's derivative comes with the raised index $\mu_1+\frac12$. In \cref{ex:mixed} this gives the leading term at $n^{-1/6}$ and the first correction at $n^{-1/3}$ as integrals over the wall $\{y=0\}$ against $x^{-1/3}dx$ and $x^{-2/3}dx$, and the second correction at $n^{-1/2}$ is the first place where a logarithm and the other wall appear.

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (constant amplitude and constant field a)
% Lean: the nonconstant-amplitude tie formulas are derivations.
\paragraph{Ties.} At a tie of $c$ walls the top logarithm is \eqref{eq:empirical_graded}, and the lower ones follow the Laurent computation of \cref{sec:tiers} with $\Gamma$ replaced by $S$. For \cref{ex:planes} at $\mu=1/2$, with $\eta_s=\eta\,S_s(\zeta)$ evaluated on a slice $z=$ const,
\[
c_{1/2,1}=\frac{\eta(0,0)S_{1/2}(\zeta(0,0))}4,\qquad c_{1/2,0}=-\frac{\eta(0,0)\,\partial_\nu S_\nu(\zeta(0,0))|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}x\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}y\,dy
\]
per quadrant and per $z$: the coefficient of $n^{-1/2}\log n$ is the fluctuation function of the field on the axis, and the coefficient of $n^{-1/2}$ is its index derivative there plus finite parts of $\eta S_{1/2}(\zeta)$ along the two planes. Summing the four quadrants, each with its own representative of the field, and integrating over $z$ gives the coefficients for this example: the sample enters the leading term through the values of the field on the axis, and the first correction through its values on the planes as well.

% Lean @ d56efc8: Grammar/EmpiricalResolvedContinuity.lean: Grammar.SmoothEngine.ResolvedData.exists_resolvedCoeff_top_bound (locally Lipschitz in the chart jets)
\subsection{How much of the field is seen}

Each coefficient depends on the field only through finitely many of its normal jets on the closed cube, of an order fixed by $\mu$: the values on the resonant faces for the leading term, first derivatives for the first correction, and so on, exactly as for the observable in \cref{thm:jet}. For the top logarithmic coefficient at each exponent, on admissible observables, this dependence is continuous and locally Lipschitz on jet balls: if two fields have jets of the relevant order within $\delta$ of each other on the closed cube, the corresponding coefficients differ by at most a constant times $\delta$. Together with the uniformity of the remainder in \cref{thm:empirical_expansion} this is what the passage to the Gaussian limit needs for those coefficients.
```

## sections/10_limit.tex
```latex
\section{The limit field}\label{sec:limit}

For a fixed sample the expansion of $Z_n[f]$ is deterministic. Its coefficients are random through the field, and the question of how they behave as the sample grows is a question about the field alone, since the geometry does not move. This section records what is known: the field converges to a Gaussian process, the coefficients converge with it, and averaging over the sample can be carried out for the fluctuation function at a single point, with a threshold.

% Lean @ d56efc8: Grammar/EmpiricalCoeffDistribution.lean: Grammar.SmoothEngine.ResolvedData.tendstoInDistribution_resolvedCoeff_top, Grammar.SmoothEngine.ResolvedData.realizableJet
% Lean @ d56efc8: Grammar/EmpiricalBranchJets.lean: Grammar.SmoothEngine.ResolvedData.coeffOnJets
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/ChartLaw.lean: tendstoInDistribution_chartField
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/DownstairsFidi.lean: tendstoInDistribution_empDeformation_fidi
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/LeadingLaw.lean: tendstoInDistribution_evidenceObs_div_leading
\subsection{Convergence in law of the coefficients}

By Watanabe's theorem \citep[Thm~6.2]{greybook} the signed-root process $\xi_n$ of \cref{sec:setting} converges in law, as $n\to\infty$, to a centred Gaussian process $G$ on the resolution with covariance $\Cov_X\big(a(X,u),a(X,u')\big)$, where $a$ is the function of the standard form: in a chart with $K\circ\pi=u^{2k}$ it is defined by $\log\big(q(x)/p(x\mid\pi(u))\big)=u^k\,a(x,u)$, so that $\E_X\,a(X,u)=u^k$ and $\psi_n\circ\pi=\pm n^{-1/2}\sum_i\big(u^k-a(x_i,u)\big)$ with the sign of $u^k$; the orthantwise representatives of $\psi_n$ and of its limit are $\pm\xi_n$ and $\pm G$ with that sign, so their covariance carries the factor $\operatorname{sgn}(u^k)\operatorname{sgn}(u'^k)$. This convergence is a statement about the process as a function on the resolved manifold.

The top coefficients of \cref{thm:empirical_expansion}, on admissible observables, depend on the field only through finitely many normal jets on the chart cubes, continuously and locally Lipschitz (\cref{sec:empirical}). Hence, if the vector of jets of $\hat\psi_n$ of the relevant order, taken jointly over all charts and orthants, converges in law, these coefficients converge in law to the same functionals evaluated on the jets of $G$, and by the same continuity jointly for any finite set of exponents (the formal statement is for one exponent and takes the limiting jets to be jets of smooth root fields, which is the case when $G$ has smooth orthantwise representatives); and since the remainder of the expansion at cutoff $U$ is $O_P(n^{-U}(\log n)^{d-1})$ under tightness of the jet bounds, the truncation of $Z_n[f]$ at any cutoff is accurate to that order in probability. In particular
\[
n^{\lambda}(\log n)^{-(m-1)}Z_n[f]\ \Longrightarrow\ \frac1{(m-1)!}\sum_{\text{orthants}}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat G)\,d\Rres^{\lambda,\pm}_m ,
\]
the leading coefficient evaluated on the Gaussian field along the leading stratum, with $\hat G$ its one-sided limits on the walls, for $f$ admissible at depth $m$, and the analogous statements hold for the top coefficient at every retained exponent. The convergence of the face jets of the empirical process is a statement about the sample and the model, a functional central limit theorem for finitely many derivatives of $\psi_n$ on the resolution; it is the hypothesis under which the limit theorems are proved, and it is not derived from the geometry. For the leading coefficient only the values on the leading stratum are needed, and there the convergence is Watanabe's theorem itself.

\subsection{Averaging over the sample: the fluctuation function of a Gaussian}

For a single centred Gaussian value $a\sim N(0,v)$, Fubini gives
% Lean @ d56efc8: Grammar/GaussianFluctuationScalar.lean: Grammar.integral_fluctuation_gaussianReal'
% Lean @ d56efc8: Grammar/GaussianThreshold.lean: Grammar.lintegral_gaussMomentJ_lt_top_iff (finite iff beta v < 2)
% Lean @ d56efc8: Grammar/WickEnvelope.lean: Grammar.integral_empCoeff_gaussian_wick_of_exp_moment (the Wick series below)
\begin{equation}\label{eq:gaussian_average}
\E\,S_\lambda(a)=\int_0^\infty t^{\lambda-1}e^{-t}\,\E e^{a\sqrt t}\,dt=\int_0^\infty t^{\lambda-1}e^{-(1-v/2)t}\,dt=\Gamma(\lambda)\Big(1-\frac v2\Big)^{-\lambda} ,
\end{equation}
finite exactly when $v<2$, and $+\infty$ otherwise. First, the expected leading coefficient of $Z_n[f]$ in the Gaussian limit is the population coefficient with the amplitude reweighted by $(1-v(x)/2)^{-\lambda}$ along the leading stratum, where $v(x)$ is the variance of the limit field at the point $x$: averaging and expanding do not commute, and $\E\,C(G)\ne C(0)$ even though $\E\,G=0$, because the coefficients are nonlinear in the field through the fluctuation function. Second, the Gaussian limiting leading coefficient need not be integrable: if the variance of the limit field exceeds $2$ on a set of positive residue measure of the leading stratum, its expectation is infinite. This is a statement about the limit object and about the failure of uniform integrability, not about finite samples: for the renormalised $K_n$ of \cref{sec:setting} one has $\E\,e^{-nK_n(w)}=\prod_i\E_q[p(x_i\mid w)/q(x_i)]=1$, so $\E\,Z_n[1]=\int\varphi$ exactly, and the expectation of the finite-sample evidence cannot be exchanged with the asymptotic limit. In the generating identity \eqref{eq:generating} the same threshold appears as the radius of convergence of the Wick series $\sum_j(2^jj!)^{-1}c^{\mathrm{pop}}_{\mu+j,q}(\eta\,W^j)$, obtained by taking expectations term by term, with $W(u)$ the variance of the scaled field $u^k\zeta(u)$ at each point of the cube: odd terms vanish, even ones contribute $(2j)!/(2^jj!)$ times the variance power, and the sum is $e^{W/2}$ distributed over the shifted exponents. The series converges under an exponential moment $\E\,e^{\delta\|J_R\zeta\|^2}<\infty$ with $\delta>\frac14$, where $J_R\zeta$ is the vector of derivatives of $\zeta$ of order at most $R$ on the cube and $R$ is fixed by $\mu$, a sufficient uniform-integrability condition that is considerably stronger than the pointwise threshold $v<2$ on the variance $v$ of $\zeta$ itself: the averaged frozen integrand has phase $-nu^{2k}+nW(u)/2=-nu^{2k}(1-v(u)/2)$, so the threshold is on $v$, not on $W=u^{2k}v$, which vanishes on the walls.

None of this affects the posterior. The posterior expectation is a ratio, bounded by $\|f\|_\infty$ for every sample, and its averaged behaviour is a different question, taken up in \cref{sec:averaging}. The threshold concerns the unnormalised evidence only.

\subsection{What is a hypothesis}

The picture of this section rests on three inputs of different standing. That the top coefficients are continuous functionals of finitely many jets of the field on admissible observables, and that the remainder is uniform on jet balls, are theorems of the smooth theory. That the empirical process converges to a Gaussian field on the resolution is Watanabe's theorem, consumed as such. That the finitely many normal derivatives of the empirical process on the faces converge jointly in law, which is what the convergence of the subleading coefficients needs, is a hypothesis about the model, plausible under the moment conditions of the standard form but not derived here; for the leading coefficient it is not needed.
```

## sections/11_posterior.tex
```latex
\section{Posterior expectations}\label{sec:posterior}

The posterior expectation of an observable is the quotient $Z_n[f]/Z_n[1]$ of two expansions on the same lattice. This section says what the quotient looks like, for a fixed sample and to all orders, and what its leading term is. The organising fact is that nothing new enters: every coefficient of the posterior expectation is a rational function of the coefficients of $Z_n[f]$ and $Z_n[1]$, and all the geometry and all the data are already in those.

\subsection{Blocks and the quotient}

Write $\ell=\log n$ and $x=n^{-1/Q}$. Collecting the logarithmic powers at a fixed exponent $\mu=j/Q$ into one polynomial gives the \emph{block}
\[
B_j(\ell)=\sum_{q\le d-1}c_{j/Q,q}\,\ell^q,\qquad Z_n\sim\sum_jB_j(\log n)\,n^{-j/Q}=\sum_jB_j(\ell)\,x^j ,
\]
so that an expansion in our scale is a power series in $x$ with coefficients polynomial in $\ell$. Blocks rather than individual coefficients are the right unit for division: the inverse of the leading block $B_0(\ell)$ of the denominator is a rational function of $\ell$, not a polynomial. The quotient of two expansions is therefore a power series in $x$ over the field $\R(\ell)$ of rational functions in $\log n$, an enlargement of the scale of \cref{sec:scale} in which the logarithmic factors need no longer be polynomial, and its coefficients, the \emph{quotient blocks}
\begin{equation}\label{eq:quotient_blocks}
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) ,
\end{equation}
are computed by the ordinary recursion for the quotient of power series, with $A_j,B_j$ the blocks of numerator and denominator counted from the first exponent at which the denominator is nonzero.

% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO'
% Lean @ d56efc8: Grammar/QuotientBlocks.lean: Grammar.quotientBlocks (def), Grammar.sum_mul_quotientBlocks
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/PosteriorAllOrders.lean: boundedInProbSeq_posteriorMean_allOrders (in probability at the diagonal)
\begin{thm}[Posterior expectation, fixed sample, all orders]\label{thm:posterior_quotient}
Let $A_j$ and $B_j$ be the blocks of the expansions of $Z_n[f]$ and $Z_n[1]$ from \cref{thm:empirical_expansion}, counted from the first exponent $\lambda$ of $Z_n[1]$ (both systems vanish below it, since $|Z_n[f]|\le\|f\|_\infty Z_n[1]$), and suppose the leading block $B_0$ is a nonzero polynomial, as it is when the prior is positive somewhere on the leading stratum. Then for every $J\ge1$,
\[
\frac{Z_n[f]}{Z_n[1]}=\sum_{j<J}R_j(\log n)\,n^{-j/Q}+O\big(n^{-J/Q}(1+\log n)^{(d-1)(J+1)}\big) ,
\]
with $R_j$ the quotient blocks \eqref{eq:quotient_blocks}, kept exact as rational functions of $\log n$. Each $R_j$ may be expanded in inverse powers of $\log n$ to any order if a pure power-logarithm form is wanted.
\end{thm}

The remainder is $O$ and not $o$ at that scale: the omitted block survives at exactly the order of the bound. The theorem is deterministic algebra over the two expansions, and its content is the statement that nothing else is true at this level: the quotient of two asymptotic expansions is the formal quotient, and the terms obtained by expanding $1/Z_n[1]$ are exactly the terms of the recursion.

\subsection{The source and the connected coefficients}

The cleaner organisation of the higher posterior moments is through a source. For bounded smooth $f$,
% Lean @ d56efc8: Grammar/SourceLog.lean: Grammar.logOf, Grammar.varianceBlocks, Grammar.coeff_two_mul_coeff_two_logOf_blocks
% Lean @ d56efc8: Grammar/PosteriorVarianceExpansion.lean: Grammar.emp_variance_isBigO (posterior variance to all orders)
\begin{equation}\label{eq:source}
\partial_\varepsilon\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f]}{Z_n[1]},\qquad \partial_\varepsilon^2\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f^2]}{Z_n[1]}-\Big(\frac{Z_n[f]}{Z_n[1]}\Big)^2 ,
\end{equation}
and in general the $r$-th derivative is the $r$-th posterior cumulant of $f$. Anchoring the logarithm at $Z_n[1]$ makes it a formal logarithm of a series with constant term one, computable by a finite formula, and fixing a source order $R$ makes only the finitely many expansions of $Z_n[f^r]$, $r\le R$, enter. Writing $m_r$ for the quotient-block series of $Z_n[f^r]/Z_n[1]$, the \emph{connected coefficients} $\kappa_r=[\varepsilon^r/r!]\log\sum_rm_r\varepsilon^r/r!$ satisfy
\[
\kappa_1=m_1,\qquad\kappa_{r+1}=m_{r+1}-\sum_{i=0}^{r-1}\binom ri\kappa_{i+1}m_{r-i} ,
\]
with Cauchy products in $x$; at the level of blocks, with $q^{f}(j)$ the quotient blocks $R_j$ of $Z_n[f]/Z_n[1]$, $\kappa_2(j)=q^{f^2}(j)-\sum_{i\le j}q^f(i)q^f(j-i)$ is the all-orders expansion of the posterior variance. Connected means connected in the source variable; the result is that every posterior cumulant is a universal polynomial in the quotient blocks, and the quotient blocks are the only new objects. The posterior variance is a susceptibility in the sense of \citet{baker2025structuralinferenceinterpretingsmall}: it is the response of $\E[f\mid\Dn]$ to the tilt of the posterior by $e^{\varepsilon f}$, and for a general perturbation of the data the response is the posterior covariance of $f$ with the perturbing score, again a connected coefficient of two observables. This is the point of contact between the expansion and those measurements.

\subsection{The leading term}

At leading order the quotient reduces to the ratio of leading blocks, and the three cases of \cref{sec:population_posterior} recur with the fluctuation function inserted. Let $(\lambda,m)$ be the leading pair, assume $D_{m+1}=\varnothing$ so that the denominator's leading block is the reweighted stratum measure of $1$, and write the field frozen and the orthantwise representatives agreeing across walls, so that the reweighting is by a single function on the stratum.

\begin{itemize}
\item \emph{Generic observable.}
% Lean @ d56efc8: Grammar/EmpiricalResolvedLeading.lean: Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ_eq_integral (numerator and denominator)
% Lean @ d56efc8: Grammar/MomentKernel.lean: HasLeadingTerm.div
% Lean: the E[K | D_n] display below is a derivation.
\begin{equation}\label{eq:leading_posterior}
\frac{Z_N[f;\psi]}{Z_N[1;\psi]}\longrightarrow\langle f\rangle_{\psi}:=\frac{\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi)\,d\Rres^\lambda_m}{\int_{S^\lambda_m}S_\lambda(\hat\psi)\,d\Rres^\lambda_m}\qquad(N\to\infty,\ \psi\text{ frozen}),
\end{equation}
for every smooth $f$, with a zero numerator allowed. The diagonal and limit statements are separate: on the empirical diagonal $\E[f\mid\Dn]-\langle f\rangle_{\hat\psi_n}\to0$ in probability, by the uniform remainder, when the denominator's leading coefficient stays bounded away from zero; and in the Gaussian limit $\E[f\mid\Dn]\Rightarrow\langle f\rangle_G$ under the convergence of \cref{sec:limit}. The posterior at leading order is the residue measure on the leading stratum reweighted by the fluctuation function of the field at each point. When the leading measure is carried by a single point, or more generally when $f\circ\pi$ is constant on its support, the reweighting cancels and the leading value is $f$ at that point regardless of the field: at a point-like singularity the data cannot move the leading posterior expectation, though it can move the first correction. When the leading stratum has positive dimension the sample redistributes posterior mass along it according to $S_\lambda(\hat\psi_n)$, and since $S_\lambda$ is increasing this favours the parts of the stratum where the empirical loss dips below the population loss.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on $S^\lambda_m$ and $m'-1$ is the largest logarithmic degree at $\lambda$ with a nonzero coefficient, $\E[f\mid\Dn]\sim D_n(\log n)^{-(m-m')}$ with $D_n$ the ratio of the corresponding reweighted residue data.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$ the expectation decays as a power when some block of $Z_n[f]$ is nonzero, with a random constant given by the ratio of the first nonvanishing block of $Z_n[f]$ to the leading block of $Z_n[1]$. For $f=K$ the shift is by exactly one, and the fluctuation factors do not cancel: since $K\circ\pi=u^{2k}$ is the radial variable $t/n$, the leading value is
\[
\E[K\mid\Dn]\sim\frac1n\,\frac{\int_{S^\lambda_m}S_{\lambda+1}(\hat\psi_n)\,d\Rres^\lambda_m}{\int_{S^\lambda_m}S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m} ,
\]
which reduces to $\lambda/n$ at zero field by $S_{\lambda+1}(0)=\lambda\Gamma(\lambda)$; in the regular one-dimensional case $K=x^2$ on $[-1,1]$ with a constant signed-root field $a$, so that the two orthants carry $\pm a$, it is $(\frac12+\frac{a^2}4)/n$, the odd terms cancelling between the sides; on a single one-sided orthant the ratio $S_{3/2}(a)/S_{1/2}(a)$ is $\frac12+\frac{a^2}4+\frac a{2S_{1/2}(a)}$.
\end{itemize}

\subsection{Tied strata and the two-site phenomenon}

When the leading stratum has several components of the same depth and exponent, the sample decides how the posterior mass is distributed between them, and the outcome has a definite sign. The simplest case is two points carrying population masses $p$ and $1-p$ and posterior weights $U=S_\lambda(a_1)$, $V=S_\lambda(a_2)$, so that the posterior mass of the first point is $Q_p=pU/(pU+(1-p)V)$. If the pair $(U,V)$ is exchangeable, which is the case when the two field values form a jointly centred Gaussian pair with equal variances,
% Lean @ d56efc8: Grammar/TwoSiteExchange.lean: Grammar.twoSitePosteriorMass, Grammar.twoSiteKernel, Grammar.integral_twoSitePosteriorMass_sub, Grammar.integral_twoSitePosteriorMass_mem
\begin{equation}\label{eq:two_site}
\E\,Q_p-p=\frac{p(1-p)(1-2p)}2\,\E\Big[\frac{(U-V)^2}{(pU+(1-p)V)((1-p)U+pV)}\Big],\qquad \E\,Q_p\in\big[\min(p,\tfrac12),\max(p,\tfrac12)\big] .
\end{equation}
Here $0<p<1$, the weights are positive and measurable, and no moments of $U,V$ are needed, since the kernel is bounded by $1/\min(p,1-p)^2$. Exchangeable disorder moves the averaged posterior mass toward equal allocation: a minority component gains, a majority component loses, and the displacement is strict as soon as $p\ne\frac12$ and $U\ne V$ with positive probability. Positivity of an observable does not make its averaged posterior expectation move in a fixed direction; the indicator of a majority component decreases. And $\E[Z_n[f]/Z_n[1]]\ne\E Z_n[f]/\E Z_n[1]$ already in the simplest case, which is the concrete reason the averaged posterior is treated separately in \cref{sec:averaging}.

\subsection{Wall-crossing with data}

The candidate exponents and maximal logarithmic degrees of the posterior expansion are determined by the vanishing orders of $f$ along the walls, exactly as in the population case, and they do not depend on the sample. What the sample changes is the coefficients, at leading order only through the values of the field on the leading strata, and a sample-dependent cancellation can remove a candidate term for particular fields. As $f$ varies in a family the candidate exponent of $\E[f\mid\Dn]$ jumps at the same walls as that of $\E_\infty[f]$, by the same rational amounts. The discrete signal of \cref{sec:population_posterior} survives the passage to data; the continuous part, the coefficients, acquires a random component with the structure described in the next section.
```

## sections/12_averaging.tex
```latex
\section{Averaging over the sample: a conditional compact-base Gaussian model}\label{sec:averaging}

The results so far hold sample by sample. The average of a posterior expectation over the sample is a different object, and this short section records what is known about it at leading order, what its exact structure is, and where the theory currently stops. Throughout the section the base is a compact metric space $S$ carrying a finite nonzero Borel measure $\rho$, the field $G$ is a centred Gaussian random element of $C(S,\R)$ with continuous positive semidefinite covariance kernel $\mathcal C$ and $\E\|G\|_\infty^2<\infty$, and the observables are continuous on $S$. The exact leading stratum of \cref{sec:population} is in general neither compact nor single-sheeted, so the identification of the geometric leading object with this model, described at the end of the section, is conditional.

\subsection{The limit posterior}

At leading order the posterior lives on the leading stratum $S=S^\lambda_m$, and by \eqref{eq:leading_posterior} the posterior expectation is the normalised $S_\lambda$-reweighting of the residue measure by the field along $S$. Passing to the Gaussian limit $G$ of the field, and keeping the radial variable $t=nK\circ\pi$ as a coordinate, the limit object is the random probability measure
% Lean @ d56efc8: Grammar/QuenchedSource.lean: Grammar.compactAvg (= <f>_g), Grammar.logTilt, Grammar.compactVar
% Lean @ d56efc8: Grammar/CompactBaseQuantise.lean: Grammar.compactD (= D(g))
% Lean @ d56efc8: Grammar/GibbsJoint.lean: Grammar.gibbsJoint (= mu_g)
\begin{equation}\label{eq:gibbs}
\mu_G(dx\,dt)=\frac{t^{\lambda-1}e^{-t+G(x)\sqrt t}}{D(G)}\,d\rho(x)\,dt,\qquad D(g)=\int_SS_\lambda(g(x))\,d\rho(x) ,
\end{equation}
on $S\times(0,\infty)$, where in the intended application $S$ is a compact, orthant-labelled version of the leading stratum and $\rho$ the corresponding residue density. Its $S$-marginal has the $S_\lambda(G)$-weights and gives $\langle f\rangle_G$ for observables seen through their values on $S$; the radial variable is what makes derivatives in the field precise, the tilt in direction $h$ being the observable $\sqrt t\,h(x)$. In this form the limit posterior is a Gibbs measure with a Gaussian random Hamiltonian, and the tools of that subject apply. In particular we use replicas: independent copies $(x_1,t_1),(x_2,t_2),\dots$ drawn from the same realisation $\mu_g$, so that a product of Gibbs averages becomes a single average $\E^{\otimes r}_{\mu_g}$ over the product measure.

\subsection{Three exact identities}

Let $\mathcal C$ be the covariance kernel of $G$ on $S$ and $\langle\phi\sqrt t\rangle_g=\int\phi\,S_{\lambda+1/2}(g)\,d\rho/D(g)$ the radial-moment weighted integral.

\begin{enumerate}
% Lean @ d56efc8: Grammar/PosteriorFrechet.lean: Grammar.posteriorDeriv, Grammar.hasFDerivAt_compactAvg
\item \emph{Fr\'echet differentiability.} $g\mapsto\langle f\rangle_g$ is differentiable on $C(S,\R)$ with the sup norm ($S$ compact), with derivative $D\langle f\rangle_g[h]=\langle f\,\sqrt t\,h\rangle_g-\langle f\rangle_g\langle\sqrt t\,h\rangle_g=\Cov_{\mu_g}(f,\sqrt t\,h)$, by the ladder $\partial_aS_\lambda=S_{\lambda+1/2}$.
% Lean @ d56efc8: Grammar/CompactBaseStein.lean: Grammar.compactSqrtTimeMoment, Grammar.GaussianField.integral_eval_mul_compactAvg
% Lean @ d56efc8: Grammar/CompactBaseFinite.lean: Grammar.GaussianField (structure: measurable evaluations, E||G||^2 < oo, Gaussian fidis with kernel matrix)
% Lean @ d56efc8: Grammar/CompactBaseKernel.lean: Grammar.PSDKernel
\item \emph{Stein's identity.} For every $x_0\in S$,
\[
\E\big[G(x_0)\langle f\rangle_G\big]=\E\big[\langle f\,\mathcal C(x_0,\cdot)\sqrt t\rangle_G-\langle f\rangle_G\langle\mathcal C(x_0,\cdot)\sqrt t\rangle_G\big] ,
\]
Gaussian integration by parts on the field, which with two independent replicas of $\mu_G$ reads $\E\langle f(x_1)(\sqrt{t_1}\mathcal C(x_0,x_1)-\sqrt{t_2}\mathcal C(x_0,x_2))\rangle^{\otimes2}_G$.
\item \emph{Covariance interpolation.} With $G_s=\sqrt sG$,
% Lean @ d56efc8: Grammar/CompactBaseResponse.lean: Grammar.compactMeanResponse (= H_f), Grammar.GaussianField.integral_compactAvg_eq, Grammar.abs_compactMeanResponse_le
% Lean @ d56efc8: Grammar/GibbsJointResponse.lean: Grammar.compactMeanResponse_eq_replica (three-replica form)
\begin{equation}\label{eq:interpolation}
\E\langle f\rangle_G=\frac{\rho(f)}{\rho(S)}+\int_0^1\E\,H_f(\sqrt s\,G)\,ds,\qquad H_f(g)=\frac12\,\E^{\otimes3}_{\mu_g}\Big[(f(x_1)-f(x_2))\big(t_1\mathcal C(x_1,x_1)-2\sqrt{t_1t_3}\,\mathcal C(x_1,x_3)\big)\Big] ,
\end{equation}
with $\rho(f)=\int_Sf\,d\rho$, and $|H_f(g)|\le5\|f\|_\infty c\,(2\lambda+\tfrac14)(1+\|g\|_\infty^2)$ when $\mathcal C\le c$ on the diagonal. The averaged posterior expectation differs from the zero-field value, the population posterior expectation on the leading stratum, by an integral over the covariance amplitude of a three-replica response, and only the second moment of $\|G\|_\infty$ enters.
\end{enumerate}

% Lean @ d56efc8: Grammar/InverseEvidence.lean: Grammar.inv_compactD_le, Grammar.integrable_inv_compactD_rpow_of_isGaussian
% Lean @ d56efc8: Grammar/QuenchedSource.lean: Grammar.quenchedSource (= Psi), Grammar.abs_logTilt_le, Grammar.deriv_quenchedSource, Grammar.deriv_deriv_quenchedSource_zero
% Lean: the convergence radius log 2/||f|| of Psi is an elementary derivation.
These identities are exact and hold at every temperature and every variance; the threshold $v<2$ of \cref{sec:limit} concerns the unnormalised evidence and does not appear, since the inverse evidence $D(G)^{-1}\le\lambda e^{2}(1+\|G\|_\infty)^{2\lambda}/\rho(S)$ has all moments. Iterating \eqref{eq:interpolation} produces finite-order expansions in the covariance amplitude with exact integral remainders, in which covariance lines between replicas are the bookkeeping. The interpolation to finite order does not give a convergent series in the covariance, and the amplitude $s$ is not the asymptotic parameter $n^{-1/Q}$, so these identities describe the random leading object and its dependence on the field, not the subleading $n$-expansion. The averaged posterior cumulants are packaged by the quenched source $\Psi(\varepsilon)=\E\log\langle e^{\varepsilon f}\rangle_G$, with $\Psi'(0)=\E\langle f\rangle_G$ and $\Psi''(0)=\E\operatorname{Var}_{\mu_G}(f)$, an expected conditional variance; for bounded $f$ the elementary bound $|\langle e^{zf}\rangle_g-1|\le e^{|z|\|f\|_\infty}-1$ makes $\log\langle e^{zf}\rangle_g$ analytic and uniformly bounded on $|z|<\log2/\|f\|_\infty$, so the expansion of $\Psi$ in $\varepsilon$ converges there.

\subsection{Where the theory stops}

Two identifications separate the results of this section from a statement about the model. The first is that the restriction of the empirical process to the leading stratum converges in law to $G$ as a process on $S$, with $\rho$ the residue measure and $\mathcal C$ the covariance of the limit field; for the values on $S$ this is Watanabe's theorem, and it is what the leading term needs. The second is that the leading posterior expectation of the fixed-sample theory, which is a continuous functional of the field, is the functional $\langle f\rangle_G$ of that limit; this is a matter of matching the two constructions and, once done, gives $\lim_n\E[\E[f\mid\Dn]]=\E\langle f\rangle_G$ for every bounded $f$ with no further estimate, since $|E[f\mid\Dn]|\le\|f\|_\infty$ makes the posterior expectations uniformly integrable. The subleading averaged corrections are a further problem: they require rates for the fixed-sample remainders and for the law of the finite-$n$ field, the latter of Edgeworth type, and the exponent lattice rather than $n^{-1/2}$ decides which correction comes first. None of this is attempted here.
```

## sections/13_formalisation.tex
```latex
\section{What is a theorem}\label{sec:formalisation}

The chart expansions, the resolved coefficient constructions and stratum measures, the quotient algebra, and the compact-base Gaussian identities of this paper have formal counterparts in the Lean theorem prover, in the library \texttt{timaeus-research/grammar} (namespace \texttt{Grammar}, commit \texttt{d56efc8}), with the resolution of singularities consumed from the library \texttt{hironaka} through its axiom-free exports and the statements about the sample proved in a bridge workspace on top of the formalisation of \citet{greybook}. The declarations of the library named below depend on no axioms beyond \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}. \cref{tab:lean} lists the correspondence; the hypotheses stated in the table are those of the formal statements, which in several places are more specific than the prose above (the population chart statements allow a temperature $\beta>0$ and a box size $b>0$, the empirical ones are at unit temperature on the unit box, resolved statements are for a normalised core transport, and \texttt{ResolvedData} carries measurability of $K$, a smooth nonnegative compactly supported prior and smooth observables), and the reader should take the table as the precise version. Two features of the resolved statements deserve to be stated once. The resolved data consist of an \emph{open} set $W$ and a smooth prior with compact support inside it, and the partition function is the integral over all of $\R^d$; the assembled theorems therefore treat a prior supported in the interior of the parameter domain, and boundary walls of $W$, as in \cref{ex:mixed}, are covered only by the chart-level statements on the positive box. And the strata, the deep set and the open set $X_c$ of the formal statements are intersected with the pull-back of the closed support of the prior, so they are support-truncated versions of the sets of \cref{sec:population}. The geometric and statistical identifications not covered by these declarations are listed separately below.

\begin{table}[p]
\centering\scriptsize
\begin{tabular}{@{}>{\raggedright\arraybackslash}p{3.0cm}>{\raggedright\arraybackslash}p{6.6cm}>{\raggedright\arraybackslash}p{5.0cm}@{}}
\toprule
Statement & Hypotheses and content & Lean \\
\midrule
\multicolumn{3}{@{}l}{\emph{Population expansion (Part~II)}}\\
Chart expansion & smooth $\eta$ on the box, $k_i\ge1$: cutoff expansion on $Q^{-1}\N$, degree $\le d-1$, coefficients cutoff-independent & \texttt{smooth\_cutoffExpansion}, \texttt{smoothCoeff\_unique} \\
Resolved coefficients & atlas- and transport-independent; push-forward to $W$ intrinsic to $(K,\varphi)$ & \texttt{ResolvedData.coeff}, \texttt{coeff\_eq\_of\_transports}, \texttt{coeff\_comp\_gv} \\
Support & $c_{\mu,q}$ vanishes on observables vanishing near $\{r_\mu\ge q+1\}$ & \texttt{coeff\_eq\_zero\_of\_eventually\_zero\_resonant} \\
Graded stratum formula (\cref{thm:graded}) & $c\ge1$, $\mu>0$, $F$ smooth vanishing near $D_{c+1}$ (chart form: jets vanishing on the deep set): degrees $\ge c$ vanish; top coefficient as face integrals with constant $\Gamma(\mu)/((c-1)!\prod2k_j\alpha_j!)$ & \texttt{coeff\_eq\_zero\_of\_deep}, \texttt{coeff\_eq\_stratumSum}, \texttt{smoothCoeff\_eq\_faceSum\_top}, \texttt{faceMonoCoeff\_top} \\
Jet dependence (\cref{thm:jet}) & $c\ge1$, both observables smooth and vanishing near $D_{c+1}$: kills $\Ical_S^{\,n_\mu(P)+1}$ near the stratum; descends to the jet quotient & \texttt{coeff\_eq\_of\_memIdealPow}, \texttt{descendedCoeff} \\
Stratum measure (\cref{thm:stratum_measure}) & $c\ge1$, zero-order condition: positive measure on $X_c$ integrating tests to the coefficient, carried by $S^\mu_c$, unique among regular measures, transport-independent, representing $c_{\mu,c-1}$ on $\Ical_{c+1}$ & \texttt{ResolvedData.stratumMeasure} (\texttt{SmoothStratumMeasure.lean}), \texttt{coeff\_withF\_eq\_integral\_stratumMeasure}, \texttt{eq\_stratumMeasure\_of\_tests}, \texttt{stratumMeasure\_eq\_of\_transports} \\
Residue (\cref{thm:residue,thm:identity}) & $\mu>0$: $\Rres=\frac{(c-1)!}{\Gamma(\mu)}\nu$ equals the chart residue measure, the sum over pieces and simple faces of the face densities with $(2k_j)^{-1}$ per wall; no separate density-residue calculus & \texttt{residueMeasure}, \texttt{chartResidueMeasure\_eq\_residueMeasure} \\
Leading term (\cref{thm:leading}) & a pair $(\lambda,m)$ with $\lambda$ at most every wall exponent and $m$ at least every resonance count (the true extremal pair is one instance; attainment is not required, and for a non-attained pair the limit is zero); $F$ vanishing near $D_{m+1}$: normalised limit $=\int F\,d\nu^\lambda_m$; for $F\ge0$ positive at a realiser where the prior is positive, positivity; $\nu(X)\le c_{\lambda,m-1}(1)$, with equality if $D_{m+1}=\varnothing$ & \texttt{tendsto\_normalised\_partitionObs\_extremal}, \texttt{observableCoeff\_pos\_of\_realised}, \texttt{extremalStratumMeasure\_univ\_le}, \texttt{extremalStratumMeasure\_univ\_eq\_of\_deep\_empty} \\
RLCT & nonempty zero fibre, prior positive at every zero of $K$ in its closed support (so, since a connected component of $\{K=0\}$ meeting the support is then contained in it, every such component must be compact; the hypothesis excludes a compactly supported prior meeting a noncompact component such as a plane of \cref{ex:planes} on $\R^3$, and holds for isolated or compact zero components inside the region where the prior is positive): $\Zcal_n[1]\sim c\,n^{-\lambda}(\log n)^{m-1}$, $c>0$ & \texttt{exists\_rlct\_asymptotic} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Fluctuation function and empirical expansion (Part~III)}}\\
Ladder & $\beta,\mu>0$: $\partial_aS_\mu=\beta S_{\mu+1/2}$; recurrence; ODE; index derivatives as log weights (the Weber substitution, the parabolic-cylinder closed form and the erf formula are analytic derivations, not formalised) & \texttt{deriv\_fluctuation}, \texttt{fluctuation\_recurrence}, \texttt{fluctuation\_ode}, \texttt{mellinMom\_pow\_mul\_exp\_eq\_iteratedDeriv} \\
One-dimensional expansion & smooth $\eta,\xi$, $k,b>0$, integers $q,L$ with $2kL\le q+1+h$, $N\ge1$, $bN^{1/2k}\ge1$: $\sum_{j\le q}C_jN^{-\mu_j}+O(N^{-L})$ with $C_j=\partial^j[\eta S_{\mu_j}(\xi)](0)/(j!2k)$ by definition; explicit constant through $\xi\le M$ and bounds on the jet polynomials & \texttt{empOneDim\_expansion}, \texttt{empOneDim\_expansion\_of\_bounds}, \texttt{empOneDimCoeff\_one} \\
Chart expansion (\cref{thm:empirical_expansion}) & smooth $\eta,\zeta$, $k_i>0$: cutoff expansion, unique coefficients; remainder linear in a \texttt{FieldJetBound} constant at fixed field bound $M'$ & \texttt{emp\_cutoffExpansion}, \texttt{empCoeff\_unique}, \texttt{emp\_cutoffExpansion\_uniform} \\
Resolved expansion & bounded smooth root field: expansion on the common lattice with degree bounded by the common degree; at zero field the coefficients agree with the population ones on that lattice and degree range & \texttt{empZ\_cutoffExpansion}, \texttt{resolvedCoeff\_zero} \\
Graded empirical formula \eqref{eq:empirical_graded} & $\mu>0$, $c\ge1$, $k_i>0$, amplitude vanishing near the deep set (chart form) or observable vanishing near $D_{c+1}$ (resolved form): degrees $\ge c$ vanish; top coefficient $=$ population coefficient of $\eta S_\mu(\zeta)/\Gamma(\mu)$; branchwise stratum sum & \texttt{empCoeff\_eq\_zero\_of\_deep}, \texttt{empCoeff\_eq\_faceSum\_top}, \texttt{empCoeff\_top\_eq\_smoothCoeff}, \texttt{resolvedCoeff\_eq\_empStratumSum} \\
Empirical leading term \eqref{eq:empirical_leading} & chart-leading transport at $(\lambda,m)$, $m\ge1$, bounded root field, smooth $F$: normalised limit $=$ branchwise face formula with $S_\lambda(\hat\psi)$; for $\lambda>0$ and $F$ a test in the sense of the development (smooth, compactly supported in $X_m$) it equals $\int F\,d\nu(\hat\psi)$ & \texttt{hasLeadingTerm\_empZ}, \texttt{hasLeadingTerm\_empZ\_eq\_integral} \\
Generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1} & $k_i>0$, one resonant coordinate with $\mu_1$ strictly below every other exponent: $c_{\lambda,0}$, $c_{\mu_1,0}$ as face integrals; every other coefficient at lattice exponents $\le\mu_1$ and log degree $\le d-1$ vanishes & \texttt{empCoeff\_generic}, \texttt{empCoeff\_firstCorrection}, \texttt{tendsto\_firstCorrection} \\
Two-dimensional tie & $x^2y^2$ on the positive unit square, constant amplitude and field: $\frac{n^{-1/2}}4[S_{1/2}(a)\log n-\partial_\nu S_\nu(a)|_{1/2}]+o(n^{-1/2})$ (the nonconstant-amplitude formulas of \cref{sec:tiers,sec:first_orders} are derivations) & \texttt{tendsto\_logExample} \\
Generating identity \eqref{eq:generating} & smooth $\eta,\zeta$, $k_i>0$, lattice $\mu$, $q\le d-1$: unconditionally convergent series of population coefficients (in the form $\eta\zeta^r$ at the monomial $h+rk$) & \texttt{hasSum\_empCoeff\_population} \\
Mellin--Laurent characterisation & a cutoff expansion locally integrable on $(0,\infty)$ and bounded near $0$, on a strip: the Mellin transform is the transform of the subtracted remainder plus the principal parts; polar data with bounded remainder are unique and equal the coefficients & \texttt{mellin\_eq\_mellin\_cutoffRemainderFun\_add\_principalParts}, \texttt{polarCoeff\_unique} \\
Coefficient continuity & top depth-graded coefficient, $\mu>0$, $c\ge1$, admissible observable: locally Lipschitz in the chart jets of the branch representatives; convergence in law, one exponent at a time, under convergence in law of the jets to a limit that is itself the jet of a smooth root field & \texttt{exists\_resolvedCoeff\_top\_bound}, \texttt{tendstoInDistribution\_resolvedCoeff\_top} \\
Gaussian average & $\E\,S_\lambda(N(0,v))=\Gamma(\lambda)(1-v/2)^{-\lambda}$ and integrability for $v<2$ (the divergence for $v\ge2$ is the extended-integral statement \texttt{lintegral\_gaussMomentJ\_lt\_top\_iff}); Wick series for a Gaussian random smooth chart field whose scaled field $u^k\zeta$ has a smooth variance profile $W$, measurable jet maps, jet order at the depth of $\mu+\frac12$, and an exponential jet-norm moment with $\delta>\frac14$ & \texttt{integral\_fluctuation\_gaussianReal'}, \texttt{integral\_empCoeff\_gaussian\_wick\_of\_exp\_moment} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Expectations (Part~IV)}}\\
Quotient to all orders (\cref{thm:posterior_quotient}) & $Q>0$, two cutoff expansions vanishing below a common base exponent, nonzero leading block, $J\ge1$: quotient blocks, remainder $O(n^{-J/Q}(1+\log n)^{D(J+1)})$; in probability at the diagonal for the grey book's data model: i.i.d.\ sample, unit temperature, prior localised by a cutoff in $K$, bounded observable smooth in the charts, chart-leading atlas with a positive-weight chart realising $m$ (bridge workspace, \texttt{Bridge/PosteriorAllOrders.lean}) & \texttt{cutoff\_div\_isBigO'}, \texttt{boundedInProbSeq\_posteriorMean\_allOrders} \\
Connected coefficients & $\kappa_2=\partial^2_\varepsilon\log(Z[e^{\varepsilon f}]/Z[1])|_0$ at the block level; posterior variance to all orders under box-leading data with a nonzero denominator block, remainder $O(n^{-J/Q}(1+\log n)^{(d-1)(2J+2)})$; higher cumulants are algebra over the quotient blocks & \texttt{coeff\_two\_mul\_coeff\_two\_logOf\_blocks}, \texttt{emp\_variance\_isBigO} \\
Two-site balancing \eqref{eq:two_site} & probability space, $0<p<1$, measurable, everywhere positive weights with exchangeable joint law & \texttt{integral\_twoSitePosteriorMass\_sub}, \texttt{integral\_twoSitePosteriorMass\_mem} \\
Fr\'echet derivative, Stein & compact metric base with finite nonzero measure, $\beta,\lambda>0$, continuous observables; Stein additionally for a Gaussian field with continuous PSD kernel, measurable evaluations and second sup-norm moment & \texttt{hasFDerivAt\_compactAvg}, \texttt{GaussianField.integral\_eval\_mul\_compactAvg} \\
Interpolation \eqref{eq:interpolation} & same hypotheses, $\rho\ne0$, nonnegative diagonal bound $c$ on the kernel & \texttt{GaussianField.integral\_compactAvg\_eq}, \texttt{compactMeanResponse\_eq\_replica}, \texttt{abs\_compactMeanResponse\_le} \\
Inverse evidence & $\beta,\lambda>0$, $\rho\ne0$, Gaussian $C(K,\R)$-valued field: every nonnegative power of $D(G)^{-1}$ is integrable & \texttt{inv\_compactD\_le}, \texttt{integrable\_inv\_compactD\_rpow\_of\_isGaussian} \\
Quenched source & same hypotheses: $|\log\langle e^{\varepsilon f}\rangle_g|\le|\varepsilon|\,\|f\|$; $\Psi'(0)$, $\Psi''(0)$ (the convergence radius is an elementary derivation) & \texttt{abs\_logTilt\_le}, \texttt{deriv\_quenchedSource}, \texttt{deriv\_deriv\_quenchedSource\_zero} \\
\bottomrule
\end{tabular}
\caption{Formal counterparts of the statements of this paper. Names are declarations of \texttt{timaeus-research/grammar} at commit \texttt{d56efc8}, in the namespaces \texttt{Grammar}, \texttt{Grammar.SmoothEngine} and \texttt{Grammar.SmoothEngine.ResolvedData}, unless stated; the bridge statement about the sample lives in the workspace on the grey book formalisation.}
\label{tab:lean}
\end{table}

\paragraph{What is not proved.}
\begin{itemize}
\item The finite-part form \eqref{eq:tier2} for one resonant coordinate at normal order $\alpha\ge2$ when the amplitude does not vanish at the corner and $\mu$ exceeds another wall's exponent; the formalised coefficient formula performs the Taylor subtraction but its closed evaluation is not written. Likewise the closed form of the lower logarithmic coefficients at ties for nonconstant data; the $x^2y^2$ formulas of \cref{sec:first_orders}, the Weber reduction and the Gaussian integration identities are analytic derivations within established machinery, not formalised theorems and not open problems.
\item The convergence in law of the normal derivatives of the empirical process on the faces, needed for the subleading coefficients, together with the statistical hypotheses of \cref{sec:setting} that would imply it; the identification of the fixed-sample leading posterior functional, which lives on the noncompact orthant-labelled leading stratum, with $\langle f\rangle_G$ of the compact-base model of \cref{sec:averaging}; and the continuity and convergence in law of the lower logarithmic coefficients, for which only the top depth-graded coefficients are covered by the cited declarations. All are conditional statements in the present text.
\item The convergence of the fluctuation zeta function on the strip $\operatorname{Re}s<\lambda$ is derived in the bridge from the standard form under its moment hypotheses (\texttt{fluctuationZeta\_eq\_mellinContinuation\_of\_bounded\_std}); a chart-level Mellin identity for the frozen integral, which needs no statistical input, is not yet in the library.
\item The averaged subleading corrections of \cref{sec:averaging}.
\item A manifold-level residue calculus for densities: the residue is defined as a measure and identified with the face densities in charts; the operation on densities is not developed separately. For positive normal orders the chart presentation \eqref{eq:conormal_presentation} as normal derivatives against face densities is not a canonical decomposition; what is intrinsic is the total functional, the finite jet it depends on (\texttt{coeff\_eq\_of\_memIdealPow}) and its descent to the jet quotient (\texttt{descendedCoeff}), from which the principal symbol of \cref{sec:conormal} follows. The moment tensors of \cref{app:moment_tensors} are not used.
\end{itemize}
```

## sections/14_conclusion.tex
```latex
\section{Related work and conclusion}\label{sec:conclusion}

\paragraph{Related work.} The asymptotic expansion of the population partition function and the identification of its exponents with the real log canonical threshold are the foundation of singular learning theory \citep{watanabeAlgebraicGeometryStatistical2009,watanabe2018}, and the standard form of the empirical divergence, the fluctuation function and the Gaussian limit of the empirical process are Watanabe's. The use of the strata of a normal crossing divisor to organise the asymptotics of integrals with a phase is classical in the theory of Igusa zeta functions and motivic integration \citep{igusa2000introduction,denef1998motivicigusazetafunctions,gusein2010integration}, and the analogy with the amplitude selecting the visible features of a caustic in geometric optics is in \citet{arnold2012singularities}. Products and quotients of expansions in the scale $n^{-\mu}(\log n)^q$ are treated in \citet{paris2001asymptotics}. The identification of the fluctuation function with a parabolic cylinder function is classical from the point of view of special functions \citep{NIST:DLMF}. Gaussian integration by parts, replica identities and covariance interpolation as used in \cref{sec:averaging} are the standard tools of mean field spin glasses \citep{talagrand2011meanfield,panchenko2013sk,guerra2002thermodynamic}. On the empirical side, the local learning coefficient estimator \citep{lau2023quantifying}, susceptibilities \citep{baker2025structuralinferenceinterpretingsmall,gordon2026lang3} and patterning \citep{wang2026patterning} are the measurements whose geometric meaning the paper describes; the hypothesis that structure is encoded in the singular geometry is set out in \citet{murfet2025programssingularities}.

\paragraph{Relation to the earlier paper.} This paper subsumes the earlier account of the population expansion by Gerraty and Murfet, from which the geometric material of \cref{sec:resolution,sec:stratification,sec:normal_geometry} and \cref{app:moment_tensors} and the population wall-crossing picture are inherited, in places verbatim. The earlier paper described the coefficients through a Taylor tree, an absolutely convergent series over the Taylor coefficients of analytic data on a polydisc; that description has been dropped, because its analyticity hypotheses are not met by the smooth priors, cutoffs and limit fields of the application, and replaced by the smooth finite-jet and face-first description of Part~II. The stratum measures and the weighted logarithmic residue, the empirical expansion for smooth data with its three descriptions of the coefficients, the posterior quotient and connected coefficients, and the compact-base Gaussian identities are new here.

\paragraph{Conclusion.} A posterior expectation is a ratio of two integrals of the same kind, and each has an expansion whose coefficients are distributions supported on the resonant part of the exceptional divisor and paired with the observable; on the observables that vanish near the deeper crossings they are represented by finitely many normal derivatives integrated over one exact stratum. The strata are where the coefficients live; the observable enters through its restriction to a stratum and finitely many normal derivatives there; the data enters through the fluctuation function of the standardised empirical process evaluated on the same strata, with derivatives of the field climbing a ladder of indices. At leading order the posterior is the residue measure on the deepest stratum of lowest exponent, reweighted pointwise by the fluctuation function of the field, and a posterior expectation is the average of the observable against this random measure. The corrections follow the same pattern one stratum and one derivative at a time, and their algebra, the quotient and the connected coefficients, introduces nothing beyond the coefficients of the two integrals.

Three things are left open. The closed forms of the coefficients past the first correction, where the residue densities need finite parts and the ties need the lower Laurent data, are computations within a theory that is complete. The convergence in law of the derivatives of the empirical process on the strata is a statistical input about the model that the geometry cannot supply; the identification of the leading posterior functional with the Gibbs measure of the limit field is, by contrast, geometry, a compact branch space over the support of the prior on which the leading measure lives, and it has not been carried out. And the averaged subleading corrections require rates that the present limit theorems do not give. The shape of the answer is not open: at every order the coefficient is a canonical distribution on the resonant part of the divisor, of finite transverse order, whose associated-graded pieces pair a normal jet of the observable with a residue density and whose lower pieces carry the finite parts at the crossings; the data enters it by multiplication with the fluctuation function of the field.
```

## sections/A_chart_proofs.tex
```latex
\section{Chart-level proofs}\label{app:chart_proofs}

This appendix gives the proofs behind \cref{thm:population_expansion,thm:empirical_expansion} and the generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1}, at the level of detail at which they are formalised. The population case is the empirical case at zero field, so only the latter is treated. Throughout, $\eta$ and $\zeta$ are smooth on a neighbourhood of the closed cube $[0,1]^d$, $k_i\ge1$, and
\[
Z(n)=Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du .
\]

% Lean @ d56efc8: Grammar/EmpiricalOneDim.lean: Grammar.SmoothEngine.empOneDimCoeff, Grammar.SmoothEngine.oneDimExpConst (the constant K_{h,k,q,L}(M,C)), Grammar.SmoothEngine.empOneDim_expansion_of_bounds, Grammar.SmoothEngine.empOneDim_expansion
% Lean @ d56efc8: Grammar/EmpiricalFieldJets.lean: Grammar.SmoothEngine.jetPoly (= P_j)
\subsection{One variable}

Let $d=1$, so $Z(n)=\int_0^1\eta(u)u^he^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}du$. Substitute $u=\varepsilon x$ with $\varepsilon=n^{-1/2k}$, so that $nu^{2k}=x^{2k}$ and $\sqrt n\,u^k=x^k$:
\[
Z(n)=\varepsilon^{h+1}\int_0^{1/\varepsilon}\eta(\varepsilon x)\,e^{x^k\zeta(\varepsilon x)}\,x^h\,e^{-x^{2k}}\,dx .
\]
The factor $\eta(\varepsilon x)e^{x^k\zeta(\varepsilon x)}$ is a smooth function of $v=\varepsilon x$ for fixed $x$, and its $j$-th derivative in $v$ has the form $P_j(v,x^k)\,e^{x^k\zeta(v)}$ with $P_j(v,\tau)=\sum_{r\le j}p_{j,r}(v)\tau^r$ a polynomial in $\tau$ whose coefficients are built from derivatives of $\eta$ and $\zeta$ by the recursion $p_{0,0}=\eta$, $p_{j+1,r}=p_{j,r}'+\zeta'p_{j,r-1}$. Taylor's theorem in $v$ at $v=0$ to order $q$ gives
\[
\eta(\varepsilon x)e^{x^k\zeta(\varepsilon x)}=\sum_{j\le q}\frac{(\varepsilon x)^j}{j!}P_j(0,x^k)e^{x^k\zeta(0)}+R_q(\varepsilon x,x) ,
\]
with $|R_q(v,x)|\le\frac{|v|^{q+1}}{(q+1)!}\sup_{|v'|\le|v|}|P_{q+1}(v',x^k)|e^{x^k\zeta(v')}$. On $v\in[0,1]$ and $\tau\ge0$ one has $|P_j(v,\tau)|\le C_j(1+\tau)^j$ with $C_j$ a bound on the coefficient functions, and $\zeta\le M$; so the $j$-th term of the sum is integrable on $(0,\infty)$ against $x^he^{-x^{2k}}$, since $(1+x^k)^je^{Mx^k}x^he^{-x^{2k}}\le C\,e^{-x^{2k}/2}$, and the tail $\int_{1/\varepsilon}^\infty$ is $O(e^{-1/(2\varepsilon^{2k})})=O(e^{-n/2})$. The full integrals are
\[
\frac{\varepsilon^{h+1+j}}{j!}\int_0^\infty P_j(0,x^k)e^{x^k\zeta(0)}x^{h+j}e^{-x^{2k}}dx=\frac{n^{-\mu_j}}{j!\,2k}\int_0^\infty s^{\mu_j-1}e^{-s}P_j(0,\sqrt s)e^{\sqrt s\zeta(0)}ds=\frac{n^{-\mu_j}}{j!\,2k}\,\partial_v^j\big[\eta\,S_{\mu_j}(\zeta)\big](0) ,
\]
by $s=x^{2k}$ and the identity $\int s^{\mu-1}e^{-s}P_j(v,\sqrt s)e^{\sqrt s\zeta(v)}ds=\partial_v^j[\eta S_\mu(\zeta)](v)$, which is \eqref{eq:one_dim_coefficients} and follows by differentiating $\eta(v)S_\mu(\zeta(v))=\int s^{\mu-1}e^{-s}\eta(v)e^{\sqrt s\zeta(v)}ds$ under the integral $j$ times. The remainder contributes $\varepsilon^{h+1}\int_0^{1/\varepsilon}|R_q(\varepsilon x,x)|\,x^he^{-x^{2k}}dx\le\varepsilon^{h+1+q+1}\,C'$, which is $O(n^{-L})$ whenever $2kL\le q+1+h$. This proves the one-dimensional expansion with the constant
\[
K_{h,k,q,L}(M,C_\bullet)=\Big(\sum_{j\le q}\frac{2C_j\kappa_{h+2j}(M)}{j!}\Big)\,E_{k,L}+\frac{C_{q+1}}{q!}\,\kappa_{h+2q+2}(M)\int_0^\infty e^{-x^{2k}/2}dx ,
\]
where $\kappa_m(M)=m!\,e^{1+(M+1)^2/2}$ bounds $(1+y)^me^{My}e^{-y^2}$ against $e^{-y^2/2}$ and $E_{k,L}$ bounds the tail; the point is that $K$ depends on $(\eta,\zeta)$ only through $M$ and the finitely many $C_j$.

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.sliceExp, Grammar.SmoothEngine.faceWt (the weight w^{h_L} p(w)^{-mu})
\subsection{Fubini along a resonant coordinate}

In dimension $d=n'+1$ fix the coordinate $i_0$ and write $u=(u_{i_0},w)$. On the box the monomials split, $u^h=u_{i_0}^{h_{i_0}}w^{h_L}$ and $u^{2k}=u_{i_0}^{2k_{i_0}}p(w)$ with $p=w^{2k_L}$, and $\sqrt n\,u^k=\sqrt{np(w)}\,u_{i_0}^{k_{i_0}}$ for $w$ in the open box. Hence, by Fubini,
\begin{equation}\label{eq:fubini}
Z(n)=\int_{(0,1]^{d-1}}w^{h_L}\,I\big(np(w),w\big)\,dw,\qquad I(T,w)=\int_0^1\eta(u,w)\,u^{h_{i_0}}\,e^{-Tu^{2k_{i_0}}+\sqrt T\,u^{k_{i_0}}\zeta(u,w)}\,du ,
\end{equation}
the one-dimensional integral of the slice $(\eta(\cdot,w),\zeta(\cdot,w))$ at the effective sample size $T=np(w)$. The slices are uniformly controlled: $\zeta\le M$ on the closed cube, and the coefficient functions $p_{j,r}$ of the slice are restrictions to the line $\{w=\text{const}\}$ of smooth functions on the cube, obtained by the same recursion with $\partial_{u_{i_0}}$ in place of $d/dv$, so their bounds $C_j$ can be taken uniform in $w$. The one-dimensional estimate therefore holds for every slice with the same constant.

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.genericFaceCoeff, Grammar.SmoothEngine.tendsto_firstCorrection
\subsection{Dominated convergence and the generic first correction}

Let $\lambda=\mu_0$ and $\mu_1$ be the first two exponents of the coordinate $i_0$ and assume $\mu_1<(h_l+1)/2k_l$ for every $l\ne i_0$. Set $a_j(w)=\partial_u^j[\eta S_{\mu_j}(\zeta)](0,w)/(j!\,2k_{i_0})$, the one-dimensional coefficients of the slice, and
\[
B(T,w)=T^{\mu_1}\big(I(T,w)-a_0(w)T^{-\lambda}\big) .
\]
For $T\ge1$ the one-dimensional expansion with $q$ terms and cutoff $L>\mu_1$ gives $|B(T,w)-a_1(w)-\sum_{2\le j\le q}a_j(w)T^{\mu_1-\mu_j}|\le KT^{\mu_1-L}$, so $B$ is bounded on $T\ge1$ uniformly in $w$ and $B(T,w)\to a_1(w)$ as $T\to\infty$; for $T\le1$ the trivial bound $|I|\le C_0e^{\max(M,0)}$ and $T^{\mu_1-\lambda}\le1$ bound $B$ as well. The functions $a_j$ are continuous on the closed cube, since $a_j(w)=\sum_rp_{j,r}(0,w)S_{\mu_j+r/2}(\zeta(0,w))/(j!2k_{i_0})$ and $S_\nu$ is continuous. Now
\[
n^{\mu_1}\big(Z(n)-c_{\lambda,0}n^{-\lambda}\big)=\int w^{h_L}p(w)^{-\mu_1}\,B\big(np(w),w\big)\,dw,\qquad c_{\lambda,0}=\int w^{h_L}p(w)^{-\lambda}a_0(w)\,dw ,
\]
by \eqref{eq:fubini} and the identity $w^{h_L}p^{-\mu_1}B(np,w)=n^{\mu_1}w^{h_L}I(np,w)-n^{\mu_1-\lambda}w^{h_L}p^{-\lambda}a_0(w)$. The weight $w^{h_L}p(w)^{-\mu_1}=\prod_lw_l^{h_l-2k_l\mu_1}$ is integrable on the box because every exponent exceeds $-1$, which is the gap hypothesis; the integrand is dominated by a constant times this weight; and for every $w$ in the open box $np(w)\to\infty$, so the integrand converges pointwise to $w^{h_L}p^{-\mu_1}a_1(w)$. Dominated convergence gives
\[
n^{\mu_1}\big(Z(n)-c_{\lambda,0}n^{-\lambda}\big)\longrightarrow c_{\mu_1,0}=\int w^{h_L}p(w)^{-\mu_1}a_1(w)\,dw ,
\]
which is \eqref{eq:c_mu1} once $a_1$ is written out with the ladder.

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.CutoffExpansion.coeff_eq_of_twoTerm, Grammar.SmoothEngine.empCoeff_generic, Grammar.SmoothEngine.empCoeff_firstCorrection
\subsection{Reading off the coefficients}

A two-term asymptotic determines the coefficients of any cutoff expansion up to the second exponent. Precisely, if $Z$ has a cutoff expansion $c$ on $Q^{-1}\N$ with degree $\le D$, and $n^{\mu_1}(Z(n)-An^{-\lambda})\to B$ with $\lambda<\mu_1$ lattice points, then $c_{\lambda,0}=A$, $c_{\mu_1,0}=B$, and $c_{\mu,q}=0$ for every other lattice $\mu\le\mu_1$ and $q\le D$. The proof subtracts the two known terms, each of which has the obvious cutoff expansion, and uses the first-nonzero-term theorem: a cutoff expansion of a function that is $o(n^{-\mu_1})$ has no nonzero coefficient at any exponent $\le\mu_1$, because the first nonzero pair $(\mu,q)$ in the lexicographic order makes the function asymptotically equivalent to $c_{\mu,q}n^{-\mu}(\log n)^q$, which is not $o(n^{-\mu_1})$ when $\mu\le\mu_1$. Applied to the canonical expansion of \cref{thm:empirical_expansion}, this identifies $c_{\lambda,0}$ and $c_{\mu_1,0}$ with the face integrals and forces the vanishing of everything else at lattice exponents $\le\mu_1$: no logarithms at $\lambda$ or $\mu_1$, nothing between.

% Lean @ d56efc8: Grammar/EmpiricalGeneral.lean: Grammar.SmoothEngine.emp_cutoffExpansion (the face construction defining empCoeff)
% Lean @ d56efc8: Grammar/SmoothGeneral.lean: Grammar.SmoothEngine.smooth_cutoffExpansion, Grammar.SmoothEngine.smoothCoeff_unique
\subsection{The general chart expansion}

The general case, where several coordinates may resonate and every order is wanted, is organised by faces. For a face $J$ of the cube and a depth $p$ one Taylor-expands the field factor $\eta e^{\tau\zeta}$ in the $J$-normal directions to order $p$ and subtracts its Taylor polynomial in the complementary directions to the same order; the $J$-normal integrals of monomials are the one-dimensional integrals above, whose Laurent data at the resonant exponents are explicit, and the complementary integrals are integrals over the face of the Taylor-subtracted amplitude against $w^{h-2k\mu}$ with logarithmic weights $(\log w^{2k})^\ell$, convergent because the subtraction removes the terms that would diverge. The coefficient at $(\mu,q)$ is a finite sum over faces and Taylor orders of these face integrals, and the remainder of the truncation is estimated by the same one-dimensional bounds, with a constant linear in a bound on the normal jets of $\eta e^{\tau\zeta}$ of the depth. This is the construction that defines the coefficients in the formalisation; uniqueness of expansions then shows they agree with every other description, including the Laurent data of \cref{sec:tiers}, and the graded formula \eqref{eq:graded} is its evaluation at the top logarithmic order, where only the fully resonant faces of maximal depth survive and no Taylor subtraction is needed for admissible amplitudes.
```

## sections/B_fluctuation_facts.tex
```latex
\section{The fluctuation function and the Weber equation}\label{app:fluctuation_facts}

We collect the facts about $S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}dt$ used in the body, with proofs.

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.deriv_fluctuation, Grammar.fluctuation_recurrence, Grammar.fluctuation_ode, Grammar.fluctuation_one
\paragraph{Ladder and recurrence.} Differentiation under the integral, justified by the bound $t^{\mu-1}\sqrt t\,e^{-t+a\sqrt t}\le t^{\mu-1/2}e^{-t/2+a^2}$, gives $\partial_aS_\mu=S_{\mu+1/2}$ and $\partial_a^2S_\mu=S_{\mu+1}$. Integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]=(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$ over $(0,\infty)$ gives $0=\mu S_\mu-S_{\mu+1}+\frac a2S_{\mu+1/2}$, the recurrence $S_{\mu+1}=\frac a2S_{\mu+1/2}+\mu S_\mu$; rewritten with the ladder it is $S_\mu''=\frac a2S_\mu'+\mu S_\mu$. At $\mu=0$ the same computation on $[\varepsilon,T]$ gives $S_1(a)=\frac a2S_{1/2}(a)+1$ in the limit.

% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_gaussian (S_{1/2} as a Gaussian integral)
% Lean: not formalised; the Weber substitution and parabolic-cylinder closed form are analytic derivations.
\paragraph{Weber's equation.} Put $z=a/\sqrt2$ and $S_\mu(a)=e^{z^2/4}f(z)$. Then $S_\mu'=e^{z^2/4}\frac1{\sqrt2}(f'+\frac z2f)$, $S_\mu''=e^{z^2/4}\frac12(f''+zf'+\frac12f+\frac{z^2}4f)$, and substituting into the ODE and dividing by $\frac12e^{z^2/4}$ leaves $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $\nu=-2\mu$. Comparing the integral representation $D_{-\nu}(x)=\frac{e^{-x^2/4}}{\Gamma(\nu)}\int_0^\infty u^{\nu-1}e^{-u^2/2-xu}du$ \citep[\S12.5(i)]{NIST:DLMF} with the definition of $S_\mu$ after $u=\sqrt{2t}$ gives the closed form \eqref{eq:weber}. At $\mu=1/2$, $u=\sqrt t$ and completion of the square give $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}(1+\operatorname{erf}(a/2))$.

% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_iteratedDeriv (the regular orbit)
% Lean: the module structure itself is not formalised.
\paragraph{The Weyl algebra.} Let $b^\dagger=\partial_a$ and $b=2\partial_a-a$, so $[b,b^\dagger]=1$. Then $b^\dagger S_\mu=S_{\mu+1/2}$, and the recurrence at $\mu-\frac12$ gives $bS_\mu=2S_{\mu+1/2}-aS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>\frac12$, while $bS_{1/2}=2$. The number operator $b^\dagger b-(2\mu-1)$ acts on $S_{\mu+Q/2}$ by $Q$. For $\mu\notin\frac12\mathbb Z$ the definition extends to $\mu\le0$ by $S_\mu=\frac1{2\mu}bS_{\mu+1/2}$, consistently with the meromorphic continuation of \eqref{eq:weber} in $\mu$, the ladder relations persist, and the span of the $S_\mu$ along the orbit $\mu+\frac12\mathbb Z$ is a module over the Weyl algebra, doubly infinite with no lowest weight. On the orbit of $\frac12$ the span of the positive-index functions alone is not stable, since $bS_{1/2}=2$; the module is $\mathbb C[a]+\operatorname{span}\{S_{(n+1)/2}:n\ge0\}$, which contains the polynomials $\mathbb C[a]=\operatorname{span}\{b^m1\}$ as a submodule, and its quotient is the Fock representation with vacuum $S_{1/2}$.

% Lean @ d56efc8: Grammar/MellinLogWeights.lean: Grammar.SmoothEngine.mellinMom_pow_mul_exp_eq_iteratedDeriv
% Lean: the inhomogeneous Weber system is a derivation.
\paragraph{Index derivatives.} For $\nu>0$ and every $\ell$, $\partial_\nu^\ell S_\nu(a)=\int_0^\infty t^{\nu-1}(\log t)^\ell e^{-t+a\sqrt t}dt$, again by differentiation under the integral, the derivative of $t^{\nu-1}$ in $\nu$ being $t^{\nu-1}\log t$ and the bound $|\log t|^\ell t^{\nu-1}e^{-t+a\sqrt t}$ integrable. Hence for a constant $c$, $\int_0^\infty t^{\nu-1}(c-\log t)^pe^{-t+a\sqrt t}dt=(c-\partial_\nu)^pS_\nu(a)$, and $\sum_p\frac{z^p}{p!}(c-\partial_\nu)^pS_\nu=e^{zc}S_{\nu-z}$ for small $z$, the translation in the index. Differentiating the ODE $\ell$ times in $\mu$ gives the inhomogeneous equation $(\partial_\mu^\ell S_\mu)''-\frac a2(\partial_\mu^\ell S_\mu)'-\mu\,\partial_\mu^\ell S_\mu=\ell\,\partial_\mu^{\ell-1}S_\mu$, a triangular system determining the index derivatives recursively.

\paragraph{The incomplete function.} For $T>0$ let $S_\mu(a;T)=\int_0^Tt^{\mu-1}e^{-t+a\sqrt t}dt$. It has the same ladder $\partial_a^qS_\mu(a;T)=S_{\mu+q/2}(a;T)$ and index derivatives, and integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]$ over $[0,T]$ gives the inhomogeneous Weber equation $S_\mu''(a;T)-\frac a2S_\mu'(a;T)-\mu S_\mu(a;T)=-T^\mu e^{-T+a\sqrt T}$. In the applications $T=nb^{2k}$, and $S_\mu(a)-S_\mu(a;T)=\int_T^\infty t^{\mu-1}e^{-t+a\sqrt t}dt\le C_\mu e^{-T/2}e^{a^2}$ is exponentially small in $n$.

% Lean @ d56efc8: Grammar/GaussianFluctuationScalar.lean: Grammar.integral_fluctuation_gaussianReal'
% Lean @ d56efc8: Grammar/GaussianThreshold.lean: Grammar.lintegral_gaussMomentJ_lt_top_iff
\paragraph{Gaussian average.} For $a\sim N(0,v)$, $\E e^{a\sqrt t}=e^{vt/2}$, so by Tonelli $\E S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-(1-v/2)t}dt$, which is $\Gamma(\mu)(1-v/2)^{-\mu}$ for $v<2$ and $+\infty$ for $v\ge2$.
```

## sections/C_expansion_algebra.tex
```latex
\section{Multiplication and division of expansions}\label{app:expansion_algebra}

Expansions in the scale $n^{-\mu}(\log n)^q$ with exponents on a lattice $Q^{-1}\N$ and bounded logarithmic degree form an algebra, and quotients exist when the denominator's leading block is nonzero. We record the two facts in the cutoff form used throughout.

% Lean @ d56efc8: Grammar/AbstractExpansion.lean: Grammar.CutoffExpansion (def)
% Lean @ d56efc8: Grammar/CutoffExpansionUniqueness.lean: Grammar.CutoffExpansion.sub (uniqueness of coefficients)
\paragraph{Blocks.} With $x=n^{-1/Q}$ and $\ell=\log n$, a cutoff expansion $F(n)=\sum_{j<JQ}B_j(\ell)x^j+O(x^{JQ}(1+\ell)^D)$, $B_j\in\R[\ell]$ of degree $\le D$, is a truncated power series in $x$ over $\R[\ell]$, and the remainder is smaller than every retained term because $x^{JQ}(1+\ell)^D=o(x^j\ell^q)$ for $j<JQ$: powers of $x$ beat powers of $\ell$.

% Lean @ d56efc8: Grammar/PosteriorVarianceExpansion.lean: Grammar.sum_mul_sum_eq_cauchy_add_tail (Cauchy product of truncations)
% Lean: no standalone product theorem is cited; the product enters through the quotient and variance results.
\paragraph{Multiplication.} If $F$ and $G$ have cutoff expansions with blocks $A_j,B_j$ and degrees $D_1,D_2$, then $FG$ has the cutoff expansion with blocks $(A*B)_j=\sum_{i\le j}A_iB_{j-i}$ and degree $D_1+D_2$: the product of the two truncations is the truncation of the Cauchy product plus terms $x^{j}$ with $j\ge JQ$ whose coefficients are polynomials in $\ell$ of degree $\le D_1+D_2$, and the cross terms with a remainder are $O(x^{JQ}(1+\ell)^{D_1+D_2})$ since each truncation is $O((1+\ell)^{D_i})$.

% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO'
% Lean @ d56efc8: Grammar/QuotientBlocks.lean: Grammar.quotientBlocks, Grammar.sum_mul_quotientBlocks
\paragraph{Division.} Suppose $F$ and $G$ have cutoff expansions with blocks $A_j$ and $B_j$ counted from a common first exponent, and $B_0\in\R[\ell]$ is a nonzero polynomial. Define $R\in\R(\ell)[[x]]$ by $R=A/B$, that is,
\[
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) .
\]
Then for every $J\ge1$,
\[
\frac{F(n)}{G(n)}=\sum_{j<J}R_j(\ell)\,x^j+O\big(x^J(1+\ell)^{D(J+1)}\big) .
\]
The proof is the two-scale division lemma: write $G=B_0(\ell)x^{0}(1+g)$ with $g=\sum_{1\le j<J}(B_j/B_0)x^j+O(x^J(1+\ell)^D/|B_0|)$; since $B_0$ is a nonzero polynomial, $|B_0(\ell)|\ge c\,\ell^{\deg B_0}$ for large $\ell$, so $g\to0$ and $|g|\le Cx(1+\ell)^{D}$ for large $n$, and $(1+g)^{-1}=\sum_{i<J}(-g)^i+O(x^J(1+\ell)^{DJ})$. Multiplying the truncations of $F/B_0$ and $(1+g)^{-1}$ and collecting powers of $x$ gives the recursion, with the stated growth of the remainder: since $B_0$ is a nonzero polynomial, $1/B_0(\ell)=O(1)$ as $\ell\to\infty$, and the displayed logarithmic growth of the remainder is a coarse bound for the finite products that occur in the formal division; the blocks are kept as rational functions so that the bound is exact in $\ell$. Each $R_j$ can be expanded in inverse powers of $\ell$ to any order by dividing the polynomials, at the cost of exactness in $\ell$.

% Lean @ d56efc8: Grammar/SourceLog.lean: Grammar.logOf, Grammar.mul_derivative_logOf, Grammar.coeff_succ_mul_eq_sum_logOf, Grammar.two_mul_coeff_two_logOf, Grammar.coeff_two_mul_coeff_two_logOf_blocks
\paragraph{The logarithm with a source.} For a formal series $U=1+\varepsilon U_1+\varepsilon^2U_2+\cdots$ over any commutative $\mathbb Q$-algebra, $[\varepsilon^r]\log U=\sum_{j=1}^r\frac{(-1)^{j+1}}j[\varepsilon^r](U-1)^j$, a finite formula, and $U\,\partial_\varepsilon\log U=\partial_\varepsilon U$. Applied to $U=\sum_r m_r\varepsilon^r/r!$ with $m_r\in\R(\ell)[[x]]$ the quotient-block series of $Z_n[f^r]/Z_n[1]$, this gives the recursion for the connected coefficients of \cref{sec:posterior}: $\kappa_1=m_1$ and $\kappa_{r+1}=m_{r+1}-\sum_{i<r}\binom ri\kappa_{i+1}m_{r-i}$, in particular $\kappa_2=m_2-m_1^2$ blockwise.
```

## sections/D_resolution_facts.tex
```latex
\section{Resolution facts used}\label{app:resolution_facts}

\paragraph{The resolution theorem.} We use Hironaka's theorem in the form of \citet[\S11.3, Thm~3.2.1]{igusa2000introduction}, applied to $K_{\mathbb C}$ together with the complexified boundary functions of $W$ and the complexification of an analytic positive factor of the prior where one is assumed: a proper holomorphic $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$, an isomorphism off the union of $\{K_{\mathbb C}=0\}$ and the singular locus of the boundary, with $(K_{\mathbb C}\circ\pi)^{-1}(0)$ a normal crossing divisor along whose components $K_{\mathbb C}\circ\pi$ and the Jacobian vanish to constant orders. Since $K$ is real the centres of the blow-ups can be taken real \citep{bierstone1997canonical}, so that $U_{\mathbb C}$ carries an anti-holomorphic involution lifting conjugation, whose fixed locus is the real resolution $U$. At a real point through which exactly the components $E_1,\dots,E_p$ pass, the local coordinates can be chosen equivariant, hence real, and the normal form \eqref{eq:local_normal_form} holds with real units. Nonnegativity of $K$ forces the exponents $a_i$ to be even: an odd exponent would change the sign of $K\circ\pi$ across the wall while the unit does not vanish. Absorbing the unit into a normal coordinate uses only that it is positive and smooth, and changes the Jacobian factor by a smooth positive function without changing the $h_i$. The orders $h_i$ include the effect of rectilinearising the domain, which the phase alone does not see: for $W=\{0\le x\le1,\ 0\le y\le x^2\}$ and $K=x^2$ the integral is $\int_0^1x^2e^{-nx^2}dx\sim\tfrac12\Gamma(\tfrac32)n^{-3/2}$, not the $n^{-1/2}$ of the phase wall $(k,h)=(1,0)$, because the blow-up that straightens the cusp contributes to the Jacobian.

\paragraph{Where the analyticity of $K$ is used.} Only here. The prior, the observable, and the cutoffs of the partitions of unity are smooth, and the expansion theorems of the body are proved for smooth data on the resolution. If $K$ is merely smooth no resolution exists in general, and the theory does not apply; if $K$ is analytic but not polynomial and a comparable polynomial exists, one may replace it by that polynomial without changing exponents or logarithmic degrees, though the coefficients change; such a polynomial need not exist.

\paragraph{Change of variables.} The pull-back $\Zcal_n[f]=\int_U(f\circ\pi)e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ is the change of variables formula for $\pi$, which is not injective on $E$ but is a diffeomorphism off $E$, a set of measure zero whose image $W_0$ has measure zero; this suffices \citep[Thm~7.26]{rudin1987real}.

\paragraph{Tubular neighbourhoods and boundary walls.} The integration domain is rectilinearised together with the phase: in each chart the coordinates are split into phase-active ones, with $k_i>0$, and the remaining ones, which include the coordinates cutting out the boundary of $W$ and are treated as parameters; the resolution is an isomorphism off $\{K=0\}$ but the domain may still need its own charts, and a boundary wall need not be a component of the divisor of $K$. On the ambient real resolution each $E_I$ is a submanifold and the tubular neighbourhood theorem applies to it, with fibres meeting no component $E_j$, $j\notin I$, because the defining equation of such an $E_j$ is a unit near $S_I$. Where a component of the divisor is itself a wall of the integration domain the admissible normal directions form an inward cone rather than a full fibre, and the statements are made orthantwise, in charts, which is how the formalisation proceeds; \cref{sec:normal_geometry} keeps the geometric discussion on the ambient resolution and imposes the domain restrictions chartwise.

\paragraph{The partition of unity.} Cover a neighbourhood $U_\varepsilon=\{K\circ\pi<\varepsilon\}$ of $E$ by normal crossing charts, each meeting only the components of one index set, and take a smooth partition of unity subordinate to this cover. The cutoffs depend on all chart coordinates and are treated as part of the smooth amplitude: they are differentiated in the normal directions along with the prior and the observable, and the face construction of \cref{app:chart_proofs} applies to the product. A cutoff constant along the normal fibres of a stratum would be convenient but is not in general available (normalising functions constant along different fibre projections destroys the constancy, and a fibre-constant function cannot be extended by zero smoothly across the normal boundary of its tube), and it is not needed: the sum over charts is independent of the choice, and only the sum is asserted to be canonical. Analytic partitions of unity do not exist, which is one of the reasons the theory is developed for smooth amplitudes.

\paragraph{Comparability.} If $g_1\asymp g_2$ are comparable nonnegative functions monomialised by the same resolution, their vanishing orders along every component agree: near a point of a component with local equation $u$, $g_i\circ\pi=\varepsilon_iu^{N_i}\cdot(\text{other factors})$, and $c_1\le g_1/g_2\le c_2$ along a curve transverse to the wall forces $N_1=N_2$ \citep[App.~B]{murfet2025programssingularities}. Hence the candidate exponents and logarithmic degrees, and the leading pair for positive amplitudes, are the same for $g_1$ and $g_2$; the coefficients are not, and a subleading candidate present for one may be absent for the other.
```

## sections/E_moment_tensors.tex
```latex
\section{Moment tensors and tubular neighbourhoods}\label{app:moment_tensors}
% Lean: not formalised; nothing in this appendix is used in the proofs of the paper (see the footnote).

The earlier account of the population expansion by Gerraty and Murfet organised the per-stratum expansion around tubular neighbourhoods of the strata and moment tensors on their normal bundles. That material is recorded here.\footnote{\textcolor{red}{This appendix is not used anywhere in the paper. The coefficient statements of \cref{sec:population,sec:empirical} are derived from the face construction of \cref{app:chart_proofs}, and the coordinate-free content is carried by \cref{sec:conormal} and \cref{thm:jet}. It is retained because the moment tensors are a convenient language for the face terms.}}

\subsection{Normal derivatives as global sections}

For a smooth function $F$ on a manifold $M$ containing a submanifold $X$, the naive normal derivatives $\partial^b_uF|_X$ in local coordinates are not intrinsic: they depend on how the coordinates along $X$ are completed to coordinates on $M$, and a nonlinear change of defining equations mixes orders. The situation is different on the normal bundle $NX$, defined by the exact sequence $0\to TX\to TM|_X\to NX\to0$, where the transition functions between local frames are linear on fibres. When $X=Y_1\cap\cdots\cap Y_p$ is a transverse intersection of hypersurfaces the conormal bundle splits canonically as in \eqref{eq:conormal_splitting}, with $\mathcal L_i$ spanned by the differentials of defining equations of $Y_i$.

\begin{lem}\label{lem:normal_deriv}
Let $X=Y_1\cap\cdots\cap Y_p$ be a transverse intersection of hypersurfaces in $M$ and let $\tilde F$ be a smooth function on a neighbourhood of the zero section in $NX$. Let $u_1,\dots,u_p$ be linear fibre coordinates on $NX$ dual to a local frame adapted to the splitting \eqref{eq:conormal_splitting}. For $b\in\N^p$ the section
\[
D_b(\tilde F)=\frac1{b!}\,\frac{\partial^{|b|}\tilde F}{\partial u^{b}}\Big|_{u=0}\;(du_1|_X)^{\otimes b_1}\otimes\cdots\otimes(du_p|_X)^{\otimes b_p}
\]
is independent of the choice of adapted linear fibre coordinates, and hence a global section of $\bigotimes_i\operatorname{Sym}^{b_i}(\mathcal L_i)$ over $X$.
\end{lem}

\begin{proof}
It suffices to treat one factor. An adapted change of frame is $u_i'=g_iu_i$ with $g_i$ a nonvanishing smooth function of the base point alone. Then $\partial_{u_i'}=g_i^{-1}\partial_{u_i}$ along the fibre and $du_i'|_X=g_i\,du_i|_X$, so the factors $g_i^{-b_i}$ and $g_i^{b_i}$ cancel; mixed derivatives are unaffected because $g_i$ does not depend on the fibre coordinates.
\end{proof}

To apply this to a function $F$ on $M$ one pulls it back to the normal bundle along a tubular neighbourhood $\Phi\colon NX\to M$, a diffeomorphism from a neighbourhood of the zero section onto a neighbourhood of $X$ that restricts to the identity on $X$, and sets
\begin{equation}\label{eq:normal_differential}
D^r_\perp(F)=\sum_{|b|=r}D_b(F\circ\Phi)\in\Gamma\big(X,\operatorname{Sym}^r(N^*X)\big) ,
\end{equation}
the \emph{normal $r$-th differential} of $F$ with respect to $\Phi$. Its dependence on $\Phi$ is exactly the dependence of a Taylor coefficient on the choice of coordinates transverse to $X$. What is intrinsic is the associated graded: $\Ical_X^{\,r}/\Ical_X^{\,r+1}\cong\Gamma(X,\operatorname{Sym}^r(N^*X))$ for the ideal $\Ical_X$ of functions vanishing on $X$, so that $D^r_\perp(F)$ is canonical for an $F$ vanishing to order $r$ along $X$, and in general the transverse $r$-jet of $F$ is canonical as a class while its splitting into homogeneous pieces is not. This is made precise in \cref{sec:jets}, where the coefficients of the expansion are shown to depend on $F$ only through its class in a quotient of the ideal of functions vanishing on the stratum; the tubular neighbourhood is a device for computing that class.

\subsection{Tubular neighbourhoods and integration along fibres}

A tubular neighbourhood of $X$ separates tangential from normal variables without choosing a metric, and this separation is what reduces the per-stratum integral to an outer integral over the stratum and inner integrals over the normal fibres. We work with densities rather than forms to avoid orientations \citep[\S16]{lee2012smooth}: a density on a $d$-manifold is a section of the line bundle $|\Lambda|$ whose local expression $a(x)\,|dx_1\cdots dx_d|$ transforms by the absolute value of the Jacobian, so that it can be integrated without choosing an orientation.

Let $|\mu|$ be a smooth positive density on a neighbourhood $V$ of $X$ in $M$ and $\Phi\colon NX\to M$ a tubular neighbourhood with $\Phi^{-1}(V)$ a bounded disc bundle over $X$. Then for integrable $F$,
\[
\int_VF\,|\mu|=\int_{\Phi^{-1}(V)}(F\circ\Phi)\,\Phi^*|\mu| .
\]
The bundle projection $\tau\colon NX\to X$ is a surjective submersion, and for a density $|\omega|$ on $NX$ whose support is proper over $X$ there is a unique density $\tau_*|\omega|$ on $X$ with
\begin{equation}\label{eq:pushforward}
\int_X\vartheta\,\tau_*|\omega|=\int_{NX}(\vartheta\circ\tau)\,|\omega|\qquad\text{for all }\vartheta\in C^\infty_c(X) .
\end{equation}
In local coordinates $x$ on $X$ and linear fibre coordinates $u$, a density on $NX$ has the form $a(x,u)|du|\,|dx|$ and its pushforward is $\big(\int_{D_x}a(x,u)\,du\big)|dx|$, with $D_x$ the fibre over $x$: the pushforward integrates out the normal variables.

\subsection{Moment tensors}

Fix a stratum $S=S_I$, a tubular neighbourhood $\Phi\colon NS\supseteq\mathcal N\to U$ with projection $\tau$ adapted to the divisor, meaning that it carries the linear fibre coordinate hyperplanes onto the components $E_i$, $i\in I$ (an arbitrary tube such as $(u,v)\mapsto(u,v+u^2)$ does not, and then the phase is not a monomial in linear fibre coordinates), and a smooth cutoff $\chi$ with compact support in the tubular neighbourhood. Write $K_S=(K\circ\pi)\circ\Phi$ for the pulled-back phase and $|\omega_S|=\Phi^*\big(\chi\,\pi^*(\varphi\,dw)\big)$ for the full pulled-back density, cutoff included; in an adapted chart with fibre coordinates $u$ and tangential coordinates $v$ the density is $|u|^{h_I}g(v,u)\,|du\,dv|$ with $g$ smooth, and after absorbing the unit of the phase $K_S=u^{2k_I}$.

% Lean: not formalised; the moment tensors are a language for the face terms; no formal counterpart (sec:formalisation, last bullet).
\begin{defn}[Moment tensor]\label{def:moment_tensor}
For $r\ge0$ the $r$-th \emph{moment tensor} is the section $\mathsf M_{S,r}(n)$ of $\operatorname{Sym}^r(NS)\otimes|\Lambda|_S$, the symmetric normal tensors with values in densities on $S$, defined by requiring, for every section $\alpha$ of $\operatorname{Sym}^r(N^*S)$ and every test $\vartheta\in C^\infty_c(S)$,
\begin{equation}\label{eq:moment_tensor}
\int_S\vartheta\,\big\langle\alpha,\mathsf M_{S,r}(n)\big\rangle=\int_{\mathcal N}(\vartheta\circ\tau)\,\alpha(\xi^{\otimes r})\,e^{-nK_S(\xi)}\,|\omega_S|(\xi) ,
\end{equation}
where $\alpha(\xi^{\otimes r})$ evaluates the symmetric $r$-linear form on $r$ copies of the fibre vector $\xi$.
\end{defn}

The right side is a density on $NS$ with fibrewise compact support, and its pushforward along $\tau$ is the density $\langle\alpha,\mathsf M_{S,r}(n)\rangle$ on $S$; the definition uses the full pulled-back density and phase and no choice of defining equations, so the tensor is intrinsic to $(K,\varphi,\chi,\Phi)$. In an adapted chart the pairing of $\mathsf M_{S,r}$ with $du^\gamma$, $|\gamma|=r$, is the \emph{dressed} moment
\begin{equation}\label{eq:dressed_moment}
\widetilde M_\gamma(v,n)=\int_{D_v}u^\gamma\,|u|^{h_I}\,e^{-nu^{2k_I}}\,g(v,u)\,du=\sum_{|\delta|\le N}\frac{g_\delta(v)}{\delta!}\,M_{\gamma+\delta}(n)+\int_{D_v}u^\gamma|u|^{h_I}e^{-nu^{2k_I}}R'_N(v,u)\,du ,
\end{equation}
with $g_\delta$ the normal Taylor coefficients of $g$ and $R'_N$ the Taylor remainder: a convergent fibre integral, equal up to a remainder to a finite combination of bare moments. Since $D^r_\perp(f\circ\pi)$ is constant along fibres, its contraction with the moment tensor is a density on $S$.

% Lean: not formalised; exact fibrewise Taylor identity, not an asymptotic statement; the asymptotic bookkeeping is the face construction (emp_cutoffExpansion / smooth_cutoffExpansion).

% The fibrewise Taylor identity is an exact identity but not an asymptotic expansion (see rem:flat); it is not
% used and is kept here commented out.
% \begin{prop}[Fibrewise Taylor identity]\label{prop:coordfree_expansion}
% For every $N$,
% \begin{equation}\label{eq:coordfree_expansion}
% \int_U\chi\,(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw)=\sum_{r\le N}\int_S\big\langle D^r_\perp(f\circ\pi),\mathsf M_{S,r}(n)\big\rangle+\int_{\mathcal N}R_N\,e^{-nK_S}\,|\omega_S| ,
% \end{equation}
% with $R_N$ the normal Taylor remainder of $f\circ\pi\circ\Phi$ of order $N$, and in an adapted chart the $r$-th term is $\sum_{|\gamma|=r}\int_SD^\gamma_\perp(f\circ\pi)(v)\,\widetilde M_\gamma(v,n)\,|dv|$.
% \end{prop}
%
% This is an exact identity, and both sides are independent of the frame: the left manifestly, the right because the pairing of a section of $\operatorname{Sym}^r(N^*S)$ with a section of $\operatorname{Sym}^r(NS)\otimes|\Lambda|_S$ is a density. What it is not, in general, is an asymptotic expansion. The remainder $R_N$ vanishes to order $N+1$ along the zero section of $NS$, but not along the adjacent walls $\{u_i=0\}$, $i\in I$, where the phase $u^{2k_I}$ still vanishes and the Boltzmann weight does not decay. For $K=x^2y^2$ and $S$ the crossing, an amplitude flat at the origin but nonzero on the axis $\{y=0,\ x>0\}$ has every normal Taylor coefficient at the crossing equal to zero, yet contributes a nonzero $n^{-1/2}$ term from the axis. The contributions along the walls belong to the shallower strata, and the correct bookkeeping, which does produce an asymptotic expansion, expands the amplitude in the normal directions of each face and subtracts along the face what has already been counted at deeper faces. That is the face construction of \cref{sec:population} and \cref{app:chart_proofs}, and the coefficient statements of this paper are derived from it, not from \eqref{eq:coordfree_expansion}. What the moment tensors contribute is the language: each face term of the face construction is a contraction of a normal jet of the amplitude with a tensor of the form \eqref{eq:moment_tensor} on that face, and the frame-independence of the contraction is what makes the resulting coefficient a functional of the transverse jet rather than of coordinates.

\paragraph{What the moment tensors know.} The $n$-dependence of $\mathsf M_{S,r}(n)$ is governed by the bare moments \eqref{eq:bare_moment}, whose asymptotics are \eqref{eq:zeta_leading}: the candidate exponent of the $\gamma$-component of the moment tensor, for a one-sided box and before the amplitude is taken into account, is the minimum over the normal directions of the shifted ratios $(h_i+\gamma_i+1)/2k_i$, with logarithmic degree one less than the number of directions attaining it; the amplitude's face jets and the parity cancellation of two-sided directions can remove the term. Increasing $\gamma_i$ in a direction that attains the minimum alone raises the exponent until another direction takes over; increasing it in one of several tied minimising directions first reduces the multiplicity; increasing it in a non-minimising direction leaves the leading pair unchanged. In the dressed moment \eqref{eq:dressed_moment} the density corrections $\delta\ne0$ are subleading in the minimising directions and can tie in the others, which is how the prior enters the corrections and not only the leading term.
```
