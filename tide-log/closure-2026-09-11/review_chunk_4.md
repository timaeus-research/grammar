# Fidelity review — dot chunk 4/6 (141 dots)

Only problematic dots are listed. Severity is implicit in the tag; entries marked *(minor)* are
hypothesis-bookkeeping rather than wrong claims.

## Random next-log / assembly paragraph (mirror L1198)

- **[mirror L1198] `dataBoxIntegral_dataTilt`** — IMPRECISE *(minor)*. Lean takes `(hs : 0 ≤ s)`; the
  sentence introduces the tilt `tilt_{β/(β+s)}` and the Laplace numerator with no sign condition on `s`.
  Fix: add qualifier `for $s\ge0$` after "at temperature $\beta+s$".

- **[mirror L1198] `tendstoUniformlyOn_nextLog_log`** — IMPRECISE. The sentence states the lemma as the bare
  implication `log n (g_n − F) → B ⇒ log n (log g_n − log F) → B/F`; Lean needs
  `(hB : ∀ x ∈ S, |B x| ≤ MB)` and `(hδ : 0 < δ) (hfloor : ∀ x ∈ S, δ ≤ F x)`.
  Fix: replace `the uniform logarithmic lemma $\log n\,(g_n-F)\to B\Rightarrow\log n\,(\log g_n-\log F)\to B/F$`
  by `the uniform logarithmic lemma ($B$ bounded, $F\ge\delta>0$) $\log n\,(g_n-F)\to B\Rightarrow\log n\,(\log g_n-\log F)\to B/F$`.

- **[mirror L1198] `tendstoUniformlyOn_scalar_mul_zero_of_bounded`** — MISLINK / IMPRECISE. The cited
  declaration is the abstract lemma "`a_N → 0` times a uniformly convergent family with bounded limit
  `→ 0` uniformly" (generic `a : ℝ → ℝ`, `E : ℝ → P → ℝ`); it says nothing about charts, exponents or
  multiplicities. The chart-level statement the sentence makes is `tendstoUniformlyOn_chart_global`
  (Grammar/ChartAllocation.lean#L123: `log N (g_i − a_i) → d_i` with `a_i = d_i = 0` for larger-exponent
  charts). Also "or a lower multiplicity are uniformly negligible" is wrong at the next-log order: the
  multiplicity-`(m−1)` charts are *not* negligible there (they feed `D₁`, as the same sentence says
  later); the Lean module docstring says "same exponent and multiplicity `≤ m−2`".
  Fix: replace `charts with a larger exponent or a lower multiplicity are uniformly negligible after the global rescaling`
  by `charts with a larger exponent, or the same exponent and multiplicity at most $m-2$, are uniformly $o(1/\log n)$ after the global rescaling`
  and relink the dot to `\leanrefL{Grammar/ChartAllocation.lean\#L123}{tendstoUniformlyOn_chart_global}`
  (or keep the present dot but move it to a parenthetical "(scale separation)").

- **[mirror L1198] `eventually_assembled_pos`** — IMPRECISE *(minor)*. Lean assumes
  `(hBc : ∀ i, Continuous (B i))` (and `K.Nonempty`); the generic section makes no continuity assumption on
  the `B i` otherwise. Fix: add qualifier `(for continuous chart coefficients $F_i,B_i$)` after
  "compact subsets of $\{A>0\}$".

- **[mirror L1198] `tendstoUniformlyOn_chartAlloc`** — IMPRECISE. The sentence says the allocation
  corrections converge "uniformly" with no domain; Lean's section variables are
  `(hK : IsCompact K)` and `(hKpos : ∀ x ∈ K, 0 < assembledLead lam mult F l m x)`, i.e. uniformly on
  compact subsets of `{A > 0}` only (the previous clause's domain does not carry over grammatically to
  the new sentence). Fix: replace `\to(d_iA-a_iD_1)/A^2$ uniformly` by
  `\to(d_iA-a_iD_1)/A^2$ uniformly on compact subsets of $\{A>0\}$`.

## Population / second-order / wall-crossing paragraph (mirror L1240)

- **[mirror L1240] `abs_origPhaseIntegral_mul_le`** — IMPRECISE *(minor)*. Lean is for the zero-phase
  chart integral at `b = 1` (`origPhaseIntegral n h k β N 1 (fun _ => 0) …`) and requires
  `(hφ : Continuous φ) (hc : Continuous c)`. The sentence says only "For a bounded observable on a
  chart … for $c\ge0$". Fix: replace `For a bounded observable on a chart,` by
  `For a bounded continuous observable $\phi$ and continuous $c$ on a population chart ($\xi=0$, $b=1$),`.

- **[mirror L1240] `population_twoTerm_chart`** — IMPRECISE *(minor)*. "every population chart integral
  with analytic amplitude" is certified at `b = 1` with `η` continuous and a holomorphic extension to a
  polydisc of radius `R > 1` whose real part agrees with `η` on `(0,1]^d`. Fix: add qualifier
  `(at $b=1$, $\eta$ continuous with a holomorphic extension to a polydisc of radius $R>1$)` after
  "analytic amplitude".

- **[mirror L1240] `population_second_order_assembled`** — CONDITIONAL-NOT-STATED. "and after finite chart
  assembly" hides the hypotheses of the Lean statement: both integrals are given as
  `Zpop N = gInt … x N + E N` / `Z' N = gInt … x' N + E' N` over the *same* chart family with zero-noise
  joint data (`hx : ∀ I v, xiCoord (x.chart I v) = 0`) and residuals with
  `E N · log N / N^{−μ*} → 0` (resp. primed). Fix: replace `and after finite chart assembly` by
  `and after finite chart assembly (both integrals decomposed over common charts with zero-noise data and residuals $o(n^{-\mu_*}/\log n)$)`.

- **[mirror L1240] `first_nonzero_locally_constant`, `population_first_nonzero_locally_constant`** —
  IMPRECISE. The sentence concludes on "that neighbourhood" (the one on which the predecessors vanish);
  Lean concludes `∀ᶠ t in 𝓝 t₀`, i.e. on some possibly smaller neighbourhood of `t₀`, and additionally
  needs `(hc : ContinuousAt (fun t => c t p.1 p.2) t₀)` (continuity of the family `X` in the population
  version). Fix: replace `$p$ is the unique first nonzero pair on that neighbourhood` by
  `$p$ is the unique first nonzero pair on a neighbourhood of $t_0$` and
  `with the same $p$` by `with the same $p$ near $t_0$`.

## §4 fluctuation-function lemma headers (mirror L1646–L1735)

- **[mirror L1646] `fluctuation_closed_form`** — IMPRECISE (definitional). The corollary identifies `S_λ`
  with the standard parabolic cylinder function `D_{−2λ}`. In Lean `parCylNeg ν x` is *defined* as the
  DLMF §12.5(i) integral `e^{−x²/4}/Γ(ν) ∫₀^∞ u^{ν−1} e^{−u²/2 − xu} du`; no Lean theorem ties `parCylNeg`
  to Weber's equation or to any independent characterisation of `D_{−ν}`. The dot therefore certifies an
  identity between two integrals, not the identification with the special function. Fix: add a
  qualifier after the display: `(in Lean, $D_{-2\lambda}$ is the DLMF~12.5.1 integral representation)`.

- **[mirror L1666] `parCylNat_weber`** — OVER-CLAIM. `lem:qho` asserts: equivalence of the QHO Schrödinger
  equation with Weber's equation (`ν = E/(ħω) − 1/2`), the general solution `D_ν(z), D_ν(−z)`,
  quantisation `ν ∈ ℕ` from square-integrability, and the Hermite reduction `eq:Dn_hermite`. The Lean
  theorem proves only that `parCylNat n z := e^{−z²/4} He_n(z)` satisfies `f'' + (n + 1/2 − z²/4) f = 0`.
  Nothing about the Schrödinger rescaling, general solution, or quantisation is formalised. Fix: move
  the dot from the lemma header to the clause `At integer order, the parabolic cylinder function reduces to a Hermite polynomial times a Gaussian`
  and add `(formalised: the Hermite–Gaussian product solves Weber's equation at order $n$)`.

- **[mirror L1696] `raiseOp_fluctuation`, `lowerOp_fluctuation`** — OVER-CLAIM (partial). The two header
  dots certify only `eq:raising_lowering`. The lemma also asserts `[b, b†] = 1` (formalised as
  `ladder_commutator`, Grammar/Ladder.lean#L40, but carrying no dot) and the `λ = 1/2` clause
  `b S_{1/2} = 2β^{−1/2}` with `ker b = ℂ e^{βa²/4}`, for which there is no Lean declaration in
  Ladder.lean. Fix: add `\leanrefL{Grammar/Ladder.lean\#L40}{ladder_commutator}` to the header and add
  the qualifier `(the $\lambda=1/2$ evaluation and $\ker b$ are not formalised)` after the last sentence
  of the lemma — or move the two existing dots onto `eq:raising_lowering`.

- **[mirror L1724] `raiseOp_Sneg`** — OVER-CLAIM (partial). `lem:extended_ladder` states both the raising
  and the lowering relation for the extension; the single header dot certifies raising only (with the
  pole-avoidance hypothesis `∀ j ≥ 1, μ − j/2 ≠ 0` on the base order). Lowering is formalised as
  `Sneg_lowering` (Grammar/Extended.lean#L45) but not linked. Fix: add
  `\leanrefL{Grammar/Extended.lean\#L45}{Sneg_lowering}` to the header.

- **[mirror L1735] `number_operator_fluctuation`, `number_operator_Sneg`** — IMPRECISE *(minor gap)*. The
  lemma covers every `λ + Q/2 ∉ {0, −1/2, −1, …}`. Lean covers `μ > 1/2` (integral regime,
  `hμ : 1/2 < μ`) and `μ − k/2` for bases `μ > 0` with `∀ j ≥ 1, μ − j/2 ≠ 0`, i.e. all orders not in
  `½ℤ`. The single admissible order `λ + Q/2 = 1/2` (where `b S_{1/2}` is a constant and the eigenvalue
  is `0`) is covered by neither declaration. Fix: add qualifier `(the case $\lambda+Q/2=1/2$ is not formalised)`
  or add a Lean lemma for `S_{1/2}`.

## Taylor-tree headers and remark (mirror L1912–L2192)

- **[mirror L1912] `headline_standard_integral`** — IMPRECISE (scope). `defn:std_integral` is for arbitrary
  `d`, `b`, and functions `ξ, η`; the cited theorem identifies the Lean chart integral with the paper's
  integral only for `d = 2`, with `ξ = dblSum x`, `η = dblSum y` weighted-summable double series
  (`WSummable ρ`, `b < ρ`), and in the variable `N = √n`. The literal general-`d` definition exists in Lean:
  `origPhaseIntegral` (Grammar/AnalyticTaylorTree.lean#L93, `∫_{(0,b]^d} η u^h e^{−βN u^{2k} + β√N u^k ξ}`,
  with `N = n`). Fix: relink to `\leanrefL{Grammar/AnalyticTaylorTree.lean\#L93}{origPhaseIntegral}`
  (keeping the present dot as a second, `d=2` dot if desired).

- **[mirror L1926] `headline_taylor_tree`** — OVER-CLAIM (as the sole header dot). The theorem is stated
  for every `d` and analytic `ξ, η` extending to `D_R`; the cited theorem is `d = 2`, WSummable data,
  finite truncation `T`, remainder `O(N^{−2T}(1 + log N))`. The general-`d` statement under the paper's
  own hypothesis *is* formalised (`thm_TaylorTree_taylor`, Grammar/TaylorTreeDerivatives.lean#L57, and
  `thm_TaylorTree_analytic'`), and is dotted only deep inside `rem:taylor_tree_lean`. The following
  `rem:taylortree_lean` ("covers the single-chart $d=2$ finite-truncation expansion") is now stale.
  Fix: add `\leanrefL{Grammar/TaylorTreeDerivatives.lean\#L57}{thm_TaylorTree_taylor}` to the theorem
  header and update `rem:taylortree_lean` to say the general-`d` statement is formalised (coefficients
  `γ ↦ Re(∂^γ F(0)/γ!)`, remainder `O(n^{−L}(1+log n)^{d−1})` for every `L`).

- **[mirror L2188] `abs_spectralCoeff_sub_le`** — IMPRECISE *(minor)*. Lean requires `(hμ : 0 < μ)`; the
  sentence states the Lipschitz bound for `A_{μ,j}` with no restriction on `μ`. Fix: replace
  `with the same $\xi(0)=a$,` by `with the same $\xi(0)=a$ and $\mu>0$,`.

## Stochastic Taylor tree and CLT paragraph (mirror L2283–L2300)

- **[mirror L2283] `headline_coefficients_in_distribution`, `headline_normalised_remainders`** —
  CONDITIONAL-NOT-STATED / OVER-CLAIM. The theorem asserts hypothesis I, the decomposition
  `Z_n[φ] = e^{−βnL_n(w₀)} Z_n^0`, an expansion over strata, coefficients converging to `C_{μ,m}(G)` with
  `G` a Gaussian process, and the ordered-remainder limit. The two header dots certify single-chart
  `d = 2` statements *conditional on* `(hX : TendstoInDistribution X l Z μ μ')` for the coefficient data;
  no CLT, no stratum assembly, no `φ`. The following `rem:strataempirical_lean` acknowledges this but is
  itself stale: it says "Not formalised: the empirical-process CLT" and "single-chart $d=2$", whereas the
  same remark's later paragraphs dot a chart-level CLT (`SampleDatum`, `CLTFiniteDim`,
  `L1SeqGaussianLimit`) and the every-`d` chart-level statements (`tendstoInDistribution_assembled`).
  Fix: add to the header `\ (formalised at chart level, conditional on convergence in distribution of the Taylor data; see \cref{rem:strataempirical_lean})`
  and delete "the empirical-process CLT ($\xi_n\to G$, \cref{prop:convergence})" from the "Not
  formalised" list, replacing it by "the identification of the chart CLT limit with $G$ and the
  assembly of the resolved charts".

- **[mirror L2300] `tendstoInDistribution_orderedRemainder`** — IMPRECISE (index off by one). The display
  normalises by `n^{−μ}(log n)^{m−1}` and targets `C_{μ,m}` (multiplicity convention, degree `m−1`) but
  the subtracted sum reads `C_{ν,q}(ξ_n) n^{−ν}(log n)^{q}` with the ordering `q > m`; in Lean
  `orderedRemainder … μ j N = (Z − ∑_{(ν,q)≺(μ,j)} C_{ν,q} N^{−ν}(log N)^q)/(N^{−μ}(log N)^j)` with `q, j`
  both log *degrees*. With `m, q` multiplicities the subtracted power must be `(log n)^{q−1}`.
  Fix: replace `C_{\nu,q}(\xi_n)n^{-\nu}(\log n)^{q}` by `C_{\nu,q}(\xi_n)n^{-\nu}(\log n)^{q-1}`.

- **[mirror L2300] `xiCoord_sampleDatum`, `etaCoord_sampleDatum`** — IMPRECISE. The sentence says the
  weighted Taylor datum of the sample is `ξ_{n,γ} b^{|γ|} = n^{−1/2} ∑_{i≤n}(c_γ(X_i) − E c_γ(X)) b^{|γ|}`
  "with the amplitude coordinates fixed". In Lean `sampleDatum … A n ω = empiricalSum … + A`, and the
  certified identity is `xiCoord (sampleDatum …) γ = (√n)⁻¹ ∑ (…) b^{|γ|} + xiCoord A γ`: the phase
  coordinates of a fixed base datum `A` are *added*, and the amplitude coordinates are those of `A`.
  Fix: replace `with the amplitude coordinates fixed` by
  `added to the phase coordinates of a fixed base datum $A$ whose amplitude coordinates are kept`.

- **[mirror L2300] `tendstoInDistribution_of_finiteCoords`** — IMPRECISE *(minor)*. Lean requires the uniform
  `L¹` tail bound for the sequence *and* for the target (`htailG : ∀ k, ∫⁻ ‖G − truncate (F k) G‖ₑ ∂P' ≤ t k`),
  plus measurability. Fix: replace `uniformly small $L^1$ truncation tails` by
  `uniformly small $L^1$ truncation tails of the sequence and of the limit`.

- **[mirror L2300] `variance_empiricalCoord_le`** — OVER-CLAIM *(minor)*. Sentence: "the coordinates of the
  normalised sums are centred with variance $\sigma_j^2$". Lean proves
  `Var[empiricalSum Y P n · j] ≤ Var[Y 0 · j]` (equality for `n ≥ 1` is asserted only in the docstring;
  centring is `integral_empiricalCoord`, not linked). Fix: replace `with variance $\sigma_j^2$` by
  `with variance at most $\sigma_j^2$`.

- **[mirror L2300] `isCompact_tailSet`** — IMPRECISE *(minor)*. "bounded subsets of $\ell^1$ with uniformly
  small tails are compact" — Lean proves compactness of the *closed* set
  `tailSet R F ε = {‖x‖ ≤ R} ∩ ⋂_m {‖x − T_{F_m} x‖ ≤ ε_m}`; an arbitrary bounded subset with small
  tails is only relatively compact. Fix: replace `bounded subsets of $\ell^1$ with uniformly small tails are compact`
  by `closed bounded subsets of $\ell^1$ with uniformly small tails are compact`.

## Summary

141 dots reviewed; 117 are faithful as written, 24 have issues (grouped above into 22 entries; several are
minor hypothesis omissions). No dot links to a declaration that says something unrelated; the one
genuine MISLINK is `tendstoUniformlyOn_scalar_mul_zero_of_bounded` (an abstract lemma cited for a
chart-specific claim, where `tendstoUniformlyOn_chart_global` is the right target). Systematic
patterns: (1) **theorem/lemma-header dots in §4 and the Taylor-tree section certify only part of the
displayed statement** — `lem:qho`, `lem:oscillator_algebra` (commutator and `λ=1/2` clause),
`lem:extended_ladder` (lowering), `defn:std_integral`/`thm:TaylorTree` (`d=2` headline instead of the
now-formalised general-`d` theorem), `thm:strataempiricalexpansion` (chart-level, conditional); in the
two Taylor-tree cases the accompanying "formalised scope" remarks are stale relative to the Lean now
landed. (2) **Generic-section hypotheses silently supplied by prose** in the L1198/L1240 paragraphs:
compactness of `K ⊆ {A>0}`, continuity of `B_i`, `s ≥ 0`, `μ > 0`, `b = 1`, zero phase, continuity of
observables, bounded `B`/floor `F ≥ δ` in the log lemma, and the chart-decomposition hypotheses of
the assembled second-order quotient. (3) Two **normalisation slips**: the sample datum omits the base
datum `A`'s phase coordinates, and the ordered-remainder display mixes the multiplicity and log-degree
conventions (`(log n)^q` should be `(log n)^{q−1}`). (4) One **definitional caveat**: `D_{−2λ}` in the
closed form is the DLMF integral representation, not independently characterised. The equation dot
`eq:expectation_leading` (`isEquivalent_quotient_powLog`) is acceptable only because the surrounding
prose ("where … are the leading terms") and the L1240 paragraph make the conditionality explicit; the
paper's positivity claim for `C` there is not certified (Lean assumes `C ≠ 0`).
