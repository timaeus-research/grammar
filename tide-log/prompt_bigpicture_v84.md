# Consult #84 — grammar Lean: #83 programme complete (R3 + free energy + residual formula + residual posterior example); planning the localisation constructor from resolution data

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
569 modules, axiom-clean). Your #83 programme is landed in full, in your order:

* CCLXIV `PartitionLocalisation` (unit 1): `SubordinatePartition R` (bounded nonnegative measurable
  `ψ_i` with the MASKED identity `∑_i 1_{A_i} ψ_i = 1` on `U = ⋃ A_i`), `ofPartition` (ordinary
  partition + relative subordination), `counting` (the cover's counting weights), prior `p ψ_i` as a
  `TubeWeight`, ★ `boltzmannIntegral_eq_sum_partition : Z_N[F] = ∑_i Z^{ofChart i}_N[F; p ψ_i]`.
* CCLXV `PartitionAssembly` (unit 2, R3): one-chart `ProductMonomialChartVar (ofChart (R.chart i)) () K`
  per chart, `ψ_i ∘ φ_i` continuous on `W_i`, per-chart pair/coefficient, `partitionLam/Deg/Coeff`
  via `hasLeadingTerm_sum_extremal`; ★ signed `hasLeadingTerm_boltzmannIntegral_of_partition`,
  ★★ `boltzmannIntegral_isEquivalent_of_partition` (`c > 0` from one tied chart with a positive
  dominant face for `p ψ_{i₀}`), ★ `tendsto_posteriorExpectation_of_partition`. Hypothesis: every chart
  has an active divisor coordinate (`hact : ∀ i`).
* CCLXVI `LeadingTermConsequences` (unit 3): generic `eventually_between` (`c/2 ≤ ratio ≤ 2c`),
  `isTheta`, ★ `tendsto_neg_log` (`−log Z − (λ log N − k log log N) → −log c`), `freeEnergy_isBigO`;
  wrappers for the scalar/variable/partition cover theorems.
* CCLXVII `VariableResidualFormula` (unit 4): ★ `tiedSum_residual_of_data` — the tied sum of a certified
  variable-unit piece atlas WITHOUT the chosen atlas: `2^{|J|} ∑_τ ∫_base β ε^s faceLeadConst
  ∫_{(0,1]^r} pieceAmp(z, τ·ε face(w)) · q_var(z, τ·ε face(w))^{−λ} · ∏_{a∉J} w_a^{h_a−2k_aλ}` with
  `q_var` RESTRICTED TO THE FACE (residual coordinates kept, as you insisted); `tiedSum_residual_of_inner`.
* CCLXVIII `VariableUnitResidualExample` (unit 5): `K = (1+x²+y²)x²y⁴` end to end: `{1}`-piece null,
  `{0,1}`-piece tied and not all-minimal, face unit `1+x²`, ★ `Z_N ~ Γ(1/4)·I·N^{−1/4}`
  (`I = ∫₀¹ t^{−1/2}(1+t²)^{−1/4} ≈ 1.9234`; the origin-frozen `2Γ(1/4)` would be wrong) and
  ★ `E_N[x²] → J/I`, `J = ∫₀¹ t^{3/2}(1+t²)^{−1/4} ≈ 0.3600`, `J/I ≈ 0.1872`, `0 < J/I ≤ 1` — your
  preferred posterior test.

Earlier (#82): `ProductMonomialChartVar` (no `unit_indep`), variable-unit cells/atlases, the leading atlas
interface, ★★ `boltzmannIntegral_isEquivalent_of_productChartsV_extremal`, posterior, tied strata,
compatibility with the scalar package (coefficient included).

## The remaining gap: from a resolution to the product package
What hironaka delivers (pinned dependency, consumed axiom-clean):
```lean
structure IsMonomialChart (F φ dom e h W) : Prop where
  isOpen : IsOpen W; subset : dom ⊆ W; analyticOnNhd : AnalyticOnNhd ℝ φ W
  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
  exists_unit : ∃ u, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧ ∀ y ∈ W, F (φ y) = u y * monomialEval y e
  exists_jacUnit : ∃ v, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧ ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h
structure PartialResolution (n) (F) (K : Set) where  -- K compact, finite charts ι, dom i compact,
  -- φ i smooth on an open nbhd of dom i, MapsTo (φ i) (dom i) K, volume (K \ ⋃ φ i '' dom i) = 0,
  -- exceptional sets E i ⊆ dom i closed null, InjOn (φ i) (dom i \ E i), jac ≠ 0 off E i,
  -- a multiplicity bound (each point of K off a null set has ≤ mult preimages).
def PartialResolution.IsMonomial R := ∀ i, ∃ e h W, IsMonomialChart F (R.φ i) (R.dom i) e h W
-- Q_all : for analytic K ≥ 0 near a zero w (K ≢ 0 near w) there is N ∈ 𝓝 w and a monomial partial resolution of N.
```
The library's adapter: `ResolutionCover.ofPartialResolution R : ResolutionCover n R.ι` (chart i =
⟨R.dom i, R.φ i, U from smooth, E i⟩); `ae_mem_iUnion_image_ofPartialResolution` (images cover `K` a.e.).
The current unconditional bridge (CCVIII/CCIX, `exponent_of_monomialResolution`): compact chart pieces
`D i = dom i ∩ φ_i⁻¹(closedBall w r')`; at each DIVISOR POINT `y₀ ∈ D i` (`K(φ_i y₀) = 0`) the one-chart
local theorem `IsMonomialChart.local_leading_term` gives, via `exists_centredChartData` (analytic strip
normalisation, `CentredChartData`: a split `σ : Fin t ⊕ Fin (n+1) ≃ Fin d` into tangential and normal
coordinates with `y₀` vanishing on the normal ones, an open `V₀ ∋ 0`, analytic positive `unit₀`, `jac₀`,
`K(φ(y+y₀)) = unit₀ y ∏ y_{nIdx j}^{2k_j}` on `V₀`, reduced tangential Jacobian exponents `hT`, pair
`(C.lam, C.mult)`), a compact region `Ω ∋ φ y₀` and `∫_Ω F e^{−NK} ~ c N^{−λ} log^{m−1}`, `c > 0`;
at non-divisor points `K ≥ K(φ y₀)/2 > 0` nearby (exponentially small); a finite subcover of the
compact pieces and Θ-comparison give the region `Rg` and `∫_{Rg} F e^{−NK} = Θ(N^{−λ*} log^{m*−1})` with
`(λ*, m*)` the extremal centred-chart pair over divisor points — identified with hironaka's small-ball
pair (`laplace_pair_eq_resolution_pair`). Only Θ, not the leading COEFFICIENT, because the local
regions `Ω` overlap and the pieces are not a partition.

What the product package needs (`ProductMonomialChartVar R i K` for a cover `R`):
`e h W W_open dom_subset monomial : IsMonomialChart K φ_i dom_i e h W; u u_cont u_ne phase_eq; v v_cont
det_eq; T T_compact T_nonempty T_zero (∀ x ∈ T, ∀ j ∈ supp e, x j = 0); b b_pos; dom_eq : dom_i =
productDom (supp e) T b (= {y | zeroOn (supp e) y ∈ T ∧ ∀ j ∈ supp e, |y j| ≤ b}); r r_meas Cr r_bound
weight_eq : ρ_i(Φ_i y) = r (zeroOn (supp e) y) on dom_i` (for a ONE-CHART cover `r = 1` automatically).
Then CCLXV (partition assembly) needs per chart: the one-chart package, `ψ_i ∘ φ_i` continuous on `W_i`,
`hact`, and for positivity one tied chart with a positive dominant face.

## Questions

**Q1 (the localisation constructor).** Given a monomial chart `(φ, dom, e, h, W)` and a divisor point
`y₀ ∈ dom` (`K(φ y₀) = 0`, so `y₀_j = 0` for `j ∈ J := supp e`... — is that right? `monomialEval y₀ e = 0`
iff some active coordinate vanishes, not all; the CENTRED normal set is `J₀ = {j ∈ supp e : y₀_j = 0}`),
construct a **sub-chart** whose domain is a centred product box `productDom J₀ T b` at `y₀`:
`T = {y₀ + z : z supported off J₀, |z| ≤ δ}` (compact, vanishing on `J₀` after translating y₀'s
J₀-coordinates, which are 0), `b` small so the box lies in `W ∩ (interior of dom?)`. Issues:
 (a) `T_zero` wants `x j = 0` for all `j ∈ supp e` (the FULL active set), but at `y₀` only `J₀ ⊆ supp e`
     vanishes; the active coordinates `j ∈ supp e ∖ J₀` are nonzero at `y₀` and their monomial factors
     `y_j^{e_j}` are units near `y₀` — they must be ABSORBED INTO THE UNIT `u` and REMOVED from `e`
     (new exponents `e' = e|_{J₀}`, `u' = u ∏_{j∉J₀} y_j^{e_j}`, continuous nonvanishing near `y₀`).
     Similarly for `h`: `h' = h|_{J₀}`, `v' = v ∏_{j∉J₀} y_j^{h_j}`. Then `IsMonomialChart K φ dom' e' h' W'`
     on `W' = W ∩ {∀ j ∈ supp e ∖ J₀, y_j ≠ 0}` — is this a lemma worth stating generally
     ("shrinking the active set at a point where the other active coordinates do not vanish")? The
     `injOn` field becomes `InjOn φ {y ∈ W' ∧ monomialEval y h' ≠ 0}` — implied by the old one since
     `monomialEval y h ≠ 0 ↔ monomialEval y h' ≠ 0` on `W'`.
 (b) The sub-chart as a `ResolutionChart`: `dom' = productDom J₀ T b ⊆ dom` (need `⊆ dom`, or at least
     `⊆ W` — the package's `dom_subset : dom' ⊆ W'`; the `ResolutionChart` also needs `E' = E ∩ dom'`,
     `InjOn φ (dom' \ E')`).
 (c) The weight: for the ONE-CHART cover of the sub-chart, `r = 1`; the assembly then needs a
     partition of unity `ψ` on the images of the sub-charts. Where do the `ψ` come from? In
     `exponent_of_monomialResolution` the pieces `Ω` overlap and a Θ-comparison is used instead. For the
     COEFFICIENT one needs an honest decomposition of `∫_{Rg} F e^{−NK}`: (i) a partition of unity
     subordinate to the images `φ(dom'_p)` of finitely many sub-charts covering a neighbourhood of the
     divisor locus in `Rg`, plus the exponentially small complement; (ii) then CCLXV with the supplied
     `ψ` (continuity of `ψ ∘ φ` on `W'`: if `ψ` is continuous on an open set containing the images,
     fine). Constructing a continuous partition of unity subordinate to a finite cover of a compact set
     by (relatively) open sets — Mathlib has `exists_continuous_sum_one_of_isOpen_isCompact`? (I recall
     `IsCompact.exists_continuous_sum_one_of_isOpen`, or `PartitionOfUnity` for `LocallyCompact`/
     `Normal` spaces: `PartitionOfUnity.exists_isSubordinate`). The sub-chart images are compact, not
     open; we need open sets `O_p ⊇ φ(dom'_p)`… but then `ψ_p` may be positive off `φ(dom'_p)` and the
     masked identity fails. Your masked formulation needs `ψ_p = 0` on `U ∖ A_p`. With compact `A_p`
     covering `U`, a partition of unity subordinate to the cover `{A_p}` in the sense `supp ψ_p ⊆ A_p`
     may not exist with continuous `ψ_p` (compact sets with empty interior…). How do you want to
     structure this? Options: (α) choose the sub-chart domains to be CLOSED BOXES whose images have
     nonempty interior covering `U` with overlaps only on boundaries → use the counting weights on a
     refined cover of non-overlapping boxes (measure-zero overlaps: the counting weight is then 1 a.e.
     and factors trivially) — i.e. the partition by indicator functions (measurable, not continuous!):
     `ψ_p = 1_{A_p}` up to null overlaps; the assembly needs `ψ_p ∘ φ_p` continuous on `W_p` — fails
     unless we DEFINE the sub-chart domains so that `ψ_p ∘ φ_p = 1` on the whole domain: which is exactly
     the case if the images are essentially disjoint and `ψ_p := 1` (i.e. the sub-charts form a
     partition of `U` up to null sets, no partition of unity needed!). Then CCLXV applies with
     `ψ = counting`?? — the counting weight of the cover of sub-charts is `1_{A_p}/∑_q 1_{A_q}` which is
     `1_{A_p}` a.e. when the overlaps are null → `ψ_p ∘ φ_p = 1` a.e. on `dom_p` but not continuous on
     `W_p`; but the ONE-CHART assembly (CCLXV) only sees the prior `p ψ_p` on chart `p`'s own domain
     where `ψ_p = 1` a.e.; the amplitude continuity is a hypothesis on the pulled-back prior, so it would
     need `ψ_p ∘ φ_p` continuous on `W_p` — replace by the constant `1` on the chart domain: we can
     use `ψ_p := 1_{A_p}` masked (measurable) with the masked identity exact up to null sets — the
     assembly needs the integrable prior `p ψ_p` on chart `p` only through its RESTRICTION to `A_p`
     (where `ψ_p = 1`): so define the per-chart prior as `p` itself (not `p ψ_p`) and prove
     `Z_N[F] = ∑_p Z^{(p)}_N[F; p]` under the ESSENTIAL DISJOINTNESS of the images (a.e. partition).
     This is the natural "box decomposition" route: no partition of unity, no continuity issue.
     (β) genuine continuous partitions of unity and shrinking; (γ) keep Θ only. Which?
 (d) The exponentially small complement: points of `Rg` outside the divisor sub-charts have `K ≥ κ > 0`
     (compactness) — contribute `O(e^{−Nκ})`; a lemma `hasLeadingTerm_of_exponentially_small` (or
     `HasLeadingTerm.add_negligible`) is needed to add such terms to a leading term (trivial with
     `HasLeadingTerm.of_dominated`? it needs a certificate at some pair; an exponentially small term is
     `o(N^{−λ} log^k)` for every pair — add a lemma `HasLeadingTerm.add_isLittleO`).
 (e) Positivity/dominant face: at a divisor point `y₀`, the dominant face of the sub-chart stratum
     `I = J₀` contains `y₀`'s tangential coordinates (foot at `y₀`), and `F(φ y₀) > 0`, `p > 0`, `v ≠ 0`,
     tangential monomial `∏_{j∈supp e'∖I}… = 1` (empty since `supp e' = J₀ = I`) — so the dominant face
     has positive measure iff the base has (the base is `T`-dimensional: `t = d − |J₀|`; for `t = 0` it
     is a point of volume 1). Fine.

**Q2 (what to prove first).** Given the above, propose the unit sequence for "the coefficient
identification from a resolution": e.g. (1) `IsMonomialChart.restrictActive`: shrinking the active set
at a point (Q1a) — a general lemma about monomial charts; (2) `IsMonomialChart.subChartBox y₀ δ b`: the
centred product sub-chart at a divisor point with `productDom` domain inside `W'`, as a
`ProductMonomialChartVar (ofChart sub) () K` (one-chart package) — this is the CONSTRUCTOR; (3) the a.e.
box decomposition of a compact region into finitely many sub-chart images + an exponentially small
remainder (the hard geometric step; depends on (c)); (4) the assembled coefficient theorem: for analytic
`K ≥ 0`, `F > 0`, a compact region `Rg` near `w`, `∫_{Rg} F e^{−NK} ~ c N^{−λ*} log^{m*−1}` with `c > 0`
EXPLICIT as a sum of face integrals — the identified LEADING COEFFICIENT of the small-ball Laplace
integral (CCIX gave the pair; this would give the constant). Is (3) realistic? What is the minimal
version (e.g. a single divisor point `w` whose preimage is a single point in a single chart — the
"one chart, one divisor point" case — where `Rg := φ(productDom …)` needs no decomposition at all and
the constructor (2) alone gives `∫_{φ(box)} F e^{−NK} ~ c N^{−λ} log^{m−1}` with the EXPLICIT `c`, refining
`local_leading_term` whose `c` is opaque)? I would start there: it upgrades CCV's identified leading
term to an explicit-coefficient statement with the product-chart formula, for every monomial chart at
every divisor point. Then the multi-chart decomposition is a separate programme.

**Q3 (the `hact` restriction of CCLXV).** Charts without active divisor coordinates (`e = 0`): `K ∘ φ = u ≠ 0`
on `W ⊇ dom`, so `K ∘ φ ≥ κ > 0` on the compact `dom` and the chart's Boltzmann integral is
`O(e^{−Nκ})`. The clean fix is the `add_isLittleO` lemma of Q1(d) and a version of
`hasLeadingTerm_boltzmannIntegral_of_partition` where the sum runs over the active charts only. Do you
agree, and is the exponential bound already available in the library in a usable form (there is
`hasLeadingTerm_boltzmannIntegral_of_no_active` for the scalar package: certificate `0` at every pair,
proved via the piece decomposition with no nonempty strata — its variable analogue is a 10-line copy)?
So: no exponential estimate needed — the empty-stratum piece theorem already gives certificate `0` at
EVERY pair. Then `HasLeadingTerm.add` with coefficient `0` handles inactive charts. Confirm.

**Q4 (anything else).** With 569 modules and 931 dots, are there statements in the paper's §3–§4 that
you now consider under-served, or a cheaper high-value target than the localisation constructor (e.g.
the `hact`-free partition theorem of Q3; a "two charts" regression through CCLXV with a genuine
partition of unity `ψ₁ + ψ₂ = 1` (e.g. `[−1,1]` covered by two overlapping charts with ramps) to
exercise the supplied-partition theorem end to end)? Rank the next 3–5 units.
