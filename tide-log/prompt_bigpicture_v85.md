# Consult #85 — grammar Lean: #84 programme complete; designing the resolved-space programme

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
573 modules, axiom-clean; every new theorem `#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Your #84 programme is landed in full, in your order, with your corrections:

* CCLXIX `VariableNoActiveAssembly` (unit 1): `IsActive` (`e.support ≠ ∅`), `activeCharts`, primed
  pair/coefficient `chartLam'/chartDeg'/chartCoeff'` (zero certificate for inactive charts via the
  variable copy of the no-active piece theorem), ★ `hasLeadingTerm_boltzmannIntegral_of_partition'`
  (no `hact`; hypothesis only `hne : (R.activeCharts Ps).Nonempty`), `partitionCoeff'_pos`,
  `boltzmannIntegral_isEquivalent_of_partition'`, `tendsto_posteriorExpectation_of_partition'`,
  `tendsto_freeEnergy_of_partition'`.
* CCLXX `MonomialChartProductBox` (units 2–3): `restrictExp e J = e.filter (· ∈ J)`, `removedExp`,
  `restrictNhd e J W = W ∩ {y | ∀ j ∈ supp e \ J, y j ≠ 0}` (open), `IsMonomialChart.restrictPhase`
  (`u' = u · y^{removedExp}` on `restrictNhd`; `h`, `v` KEPT, as you insisted), `restrictJac`, the
  product box `productBox e y₀ ρ = productDom (restrictExp e J₀).support (boxBase …) ρ` centred at `y₀`
  with `J₀ = {j ∈ supp e : y₀ j = 0}` inside `closedBall y₀ ρ ⊆ restrictNhd` (NOT required inside the
  old compact `dom`), exceptional set = null zero set of the Jacobian monomial
  (`volume_monomialEval_zero_set` via `Measure.pi_hyperplane`), `IsMonomialChart.boxChart`,
  ★ `IsMonomialChart.boxPackage hc hρ hball : ProductMonomialChartVar (ofChart (boxChart …)) () K`,
  `boxPackage_isActive` at divisor points, `exists_closedBall_subset_restrictNhd`.
* CCLXXI `LocalExplicitCoefficient` (unit 4): ★ `dominantFace_pos` (open set of feet: residual active
  coordinates in `(ρ/2, ρ)`, tangential coordinates within `ρ` of `y₀`, tangential Jacobian coordinates
  nonzero — your qualification (e)(1) handled by avoiding the finitely many Jacobian hyperplanes),
  ★★ `IsMonomialChart.boxIntegral_isEquivalent`:
  ```lean
  theorem IsMonomialChart.boxIntegral_isEquivalent (hK0 : ∀ x, 0 ≤ K x) (hK : Measurable K)
      (hdiv : monomialEval y₀ e = 0) {F} {p : TubeWeight d}
      (hFc : ContinuousOn (fun y => F (φ y)) W) (hpc : ContinuousOn (fun y => p.w (φ y)) W)
      (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
      (hFint : IntegrableOn (fun x => F x * p.w x) (φ '' productBox e y₀ ρ))
      (hFp : ∀ y ∈ Metric.closedBall y₀ ρ, 0 < F (φ y) ∧ 0 < p.w (φ y)) :
      ∃ hact hF, 0 < productCoeffV (boxPs …) … ∧
        (fun N => ∫ x in φ '' productBox e y₀ ρ, F x * p.w x * exp (-N * K x)) ~[atTop]
          fun N => productCoeffV … * N ^ (-coverLamV …) * (log N) ^ coverDegV …
  ```
  with `(coverLamV, coverDegV)` the divisor pair of the box (`boxPs_ratio : (h_j+1)/e_j` on `J₀`), the
  scope remark recorded (coefficient of the region `φ(B)`, not of a small ball).
* CCLXXII `PartitionAssemblyRegression` (unit 5): `[−1,1]` covered by the identity charts `[−1,1]` and
  `[−1/2,1/2]`, `K = x²`, ramp partition `ψ = (1 − ½β, ½β)` with `β` a bump supported in `|x| < 1/2`,
  `SubordinatePartition.ofPartition`; both charts tied at `(1/2, 0)`, `chartCoeff' = √π/2` each
  (`productCoeffV_eq : productCoeffV = √π · q.w 0` for any continuous tube weight `q` positive at `0`),
  `partitionCoeff' = √π`, ★ `∫_{[−1,1]} e^{−Nx²} ~ √π N^{−1/2}`.

Not done from #84: `HasLeadingTerm.add_isLittleO` and the exponential-remainder wrapper (Q1d).

## Standing directive
The user has asked for "the resolved-space material as a new programme of work" — i.e. your bottom
line of #84: "supply a decomposition geometry compatible with resolution images or move the partition
upstairs." I need you to DESIGN that programme concretely against the library's interfaces below, in
units I can land one file at a time (each unit ≤ ~400 lines, statement-first), and to say which parts
are honest theorems and which must remain supplied hypotheses/certificates.

## The relevant interfaces (verbatim)
```lean
structure ResolutionChart (d : ℕ) where
  dom : Set (Fin d → ℝ);  dom_compact : IsCompact dom
  φ : (Fin d → ℝ) → (Fin d → ℝ)
  U : Set (Fin d → ℝ); U_open : IsOpen U; dom_subset : dom ⊆ U; smooth : ContDiffOn ℝ 1 φ U
  E : Set (Fin d → ℝ)  -- closed null exceptional set, InjOn φ (dom \ E), jac ≠ 0 off E (fields elided)
structure ResolutionCover (d : ℕ) (ι : Type*) [Fintype ι] where chart : ι → ResolutionChart d
def ResolutionCover.image (i) := (R.chart i).φ '' (R.chart i).dom
-- coverWeight A i x = 1_{A_i}(x) / ∑_j 1_{A_j}(x)  (the counting weights), R.weight i := coverWeight R.image i
noncomputable def coverIntegral (F E) : ℝ := ∫ x in ⋃ i, R.image i, F x * exp (E x)
noncomputable def boltzmannIntegral (F K) (p : TubeWeight d) (N) : ℝ :=
  R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x)          -- Z_N[F] over ⋃ φ_i(dom_i)
-- change of variables to the charts (proved): Z_N[F] = ∑_i ∫_{dom_i} jac_i(y) ρ_i(φ_i y) F(φ_i y) p(φ_i y) e^{−N K(φ_i y)} dy
noncomputable def boltzmannChartDensity (i N K p) (y) : ℝ :=
  dom_i.indicator (fun y => jac_i y * (R.weight i (Φ_i y) * (exp (-N * K (Φ_i y)) * p.w (Φ_i y)))) y
structure TubeWeight (d) where w : (Fin d → ℝ) → ℝ; measurable; nonneg; bound; le_bound   -- bounded nonneg measurable "prior"
structure SubordinatePartition (R) where
  ψ : ι → (Fin d → ℝ) → ℝ; meas; nonneg; bound; le_bound
  masked_sum : ∀ x ∈ ⋃ i, R.image i, ∑ i, (R.image i).indicator (ψ i) x = 1
theorem boltzmannIntegral_eq_sum_partition (P : SubordinatePartition R) … :
  R.boltzmannIntegral F K p N = ∑ i, (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N
structure ProductMonomialChartVar (R) (i) (K) where
  e h : Fin d →₀ ℕ; W; W_open; dom_subset : dom_i ⊆ W; monomial : IsMonomialChart K φ_i dom_i e h W
  u; u_cont : ContinuousOn u W; u_ne; phase_eq : ∀ y ∈ W, K (φ_i y) = u y * monomialEval y e
  v; v_cont; det_eq : ∀ y ∈ W, (fderiv ℝ φ_i y).det = v y * monomialEval y h
  T; T_compact; T_nonempty; T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  b; b_pos; dom_eq : dom_i = productDom e.support T b
  r; r_meas; Cr; r_bound; weight_eq : ∀ y ∈ dom_i, R.weight i (Φ_i y) = r (zeroOn e.support y)
-- the one-chart/partition theorems take the observable F and prior p on the TARGET, with
-- `F ∘ φ_i`, `p ∘ φ_i` (or `(p ψ_i) ∘ φ_i`) continuous on W_i; the cell amplitude is
-- pieceAmp = |v| · |y_tang^h| · (F p)(φ y) restricted to the piece.
```
hironaka's `PartialResolution` (consumed axiom-clean): finitely many charts `(dom i compact, φ i smooth
near dom i, MapsTo (φ i) (dom i) K, volume (K \ ⋃ φ i '' dom i) = 0, E i ⊆ dom i closed null,
InjOn (φ i) (dom i \ E i), jac ≠ 0 off E i, a multiplicity bound)`; `IsMonomial R := ∀ i, ∃ e h W,
IsMonomialChart F (R.φ i) (R.dom i) e h W`; `Q_all` produces such a resolution of a compact
neighbourhood `N ∈ 𝓝 w` for analytic `K ≥ 0` (`K ≢ 0` near `w`). No common resolved space, no
transition maps, no compatibility between charts is exposed.

## Questions

**Q1 (the certificate interface).** Your suggestion: an assembly interface accepting **source
amplitudes plus an exact integral-decomposition certificate**. Concretely I propose
```lean
structure SourceDecomposition (Rg : Set) (F K p) where
  ι : Type; [Fintype ι]
  chart : ι → ResolutionChart d                 -- product-box charts (one-chart Var packages)
  χ : ι → (Fin d → ℝ) → ℝ                       -- SOURCE amplitudes, χ_i ≥ 0 continuous on W_i, 0 off dom_i (or off a smaller box)
  rem : ℝ → ℝ                                   -- remainder
  decomp : ∀ N ≥ 0, ∫_{Rg} F p e^{−NK} = ∑_i ∫_{dom_i} χ_i(y) |det Dφ_i y| F(φ_i y) p(φ_i y) e^{−N K(φ_i y)} dy + rem N
  rem_small : ∃ C κ > 0, ∀ N ≥ 0, |rem N| ≤ C e^{−κN}
```
and the theorem: every chart carries a `ProductMonomialChartVar` (from `boxPackage`), so with the
one-chart theorem generalised to a **source amplitude factor** `χ_i` (the current one-chart theorem's
amplitude is `(F p) ∘ φ_i · |v| · |y^h|`; `χ_i` multiplies it — it is NOT of the form `ψ ∘ φ_i` for a
target function, which is exactly what escapes the blow-up-wedge obstruction), plus
`HasLeadingTerm.add_isLittleO`, we get `∫_{Rg} F p e^{−NK} ~ c N^{−λ*} (log N)^{k*}` with `c = ∑_i c_i`
explicit and `c > 0` when one tied chart has `χ_i > 0` on a positive-measure part of its dominant face.
(a) Is this the right shape? What should be a FIELD and what a hypothesis? (b) The one-chart machinery
threads the prior through `TubeWeight` on the target; the cleanest way to add `χ_i` is a new
`ProductMonomialChartVar` field `χ` with `χ_cont : ContinuousOn χ W` and `χ_nonneg`, entering
`pieceAmp` (and the cell amplitude `A`) as a factor — the cell theorems (`VarUnitCell`) take an arbitrary
continuous amplitude, so only the piece bridge `exists_varPieceAtlas_of_chart_data` and the coefficient
bookkeeping (`tiedSum_residual_of_data`, `productCoeffV_extremal_eq_sum_minimal`) change. Alternatively
keep the package and define a "source-weighted one-chart Boltzmann integral" with `χ` in place of the
cover weight `R.weight i ∘ Φ_i` (the package already has the weight factor `r ∘ zeroOn` — but that one
factors through the INACTIVE coordinates only, which `χ` does not). Which is less invasive and still
honest? (c) `rem_small` vs `rem = o(N^{−λ*} log^{k*})`: the exponential form is what the geometry gives
(K ≥ κ off the retained boxes). Do you want both the generic `add_isLittleO` and the wrapper?

**Q2 (producing the certificate from a resolution: what is honestly provable).** With hironaka's
interface (no resolved space), which of the following can be PROVED, and which must be supplied?
 (i) For ONE chart and finitely many divisor points `y₁..y_m ∈ dom` with disjoint product boxes,
     source amplitudes `χ_k` continuous, `0 ≤ χ_k ≤ 1`, `χ_k = 1` near `y_k`, `supp χ_k ⊆ box_k`:
     `∫_{φ(⋃ box_k)} … = ∑_k ∫_{box_k} χ_k … + ∫ (1 − ∑χ_k) …`, the last term over
     `⋃ box_k \ {χ = 1}` — NOT exponentially small (the boxes contain divisor points where `1 − ∑χ_k > 0`
     unless `∑χ_k = 1` on the whole box union… which forces χ discontinuous at box boundaries meeting
     the divisor?). Hmm: on the resolved space the standard argument uses a partition of unity `∑χ_k = 1`
     on a neighbourhood of the (compact) divisor locus `{K∘φ = 0} ∩ dom`, with `supp χ_k` inside coordinate
     boxes; the remainder is supported where `∑χ_k < 1`, which is at positive distance from the divisor
     locus, so `K∘φ ≥ κ` there. On the SOURCE side (a single chart's `dom`, compact, with the divisor
     locus `Z = dom ∩ {monomialEval e = 0}` compact), Mathlib's partitions of unity for compact sets in a
     normal/locally compact space DO apply: `Z ⊆ ⋃_k int(box_k)` (boxes with nonempty interior around
     each point of `Z`, finitely many by compactness), `exists_continuous_sum_one_of_isOpen_isCompact` /
     `PartitionOfUnity`-style lemmas give `χ_k` continuous, supported in the open boxes, `∑χ_k = 1` on a
     neighbourhood of `Z`. So within ONE chart the source partition is honest. Is the per-chart statement
     "∫_{φ(dom)} F p e^{−NK} = ∑_k ∫_{box_k} χ_k … + O(e^{−κN})" provable from `IsMonomialChart` alone?
     Issue: the boxes must lie in `restrictNhd` and be centred at their divisor point (`productBox e y_k ρ_k`
     is centred and axis-aligned; the interiors cover `Z` if `ρ_k > 0`). The change of variables from
     `φ(dom)` to `dom` needs `InjOn φ (dom \ E)` and `jac ≠ 0` off `E` — available in `ResolutionChart`.
 (ii) ACROSS charts: the target region `Rg = ⋃_i φ_i(dom_i)` (a.e.) with overlapping images. The chart
     integrals with the counting weights `R.weight i` give the exact decomposition, but the counting
     weight is not continuous on the source. Your #84 diagnosis: this is the wedge obstruction. On the
     resolved space one would use the transition maps to build a global partition; hironaka exposes none.
     So the honest statement is: (ii-a) a SUPPLIED target-side `SubordinatePartition` (CCLXV/CCLXIX), or
     (ii-b) a supplied a.e.-disjointness certificate (`volume (image i ∩ image j) = 0` for `i ≠ j`) — then
     the counting weight is `1` a.e. on each image and the per-chart source partition of (i) applies chart
     by chart. Is (ii-b) worth proving as a theorem ("a.e.-disjoint assembly")? Is there a THIRD honest
     option: a "compatible resolution" structure (common resolved manifold, charts as an atlas with
     transition maps, `π : M → ℝ^d` proper, a.e. multiplicity one) defined in `Grammar` itself, with the
     global source partition of unity built by Mathlib's manifold/normal-space partitions of unity and the
     change of variables `∫_{Rg} f = ∫_M (f∘π)|det Dπ|` PROVED from the atlas data? How much of this does
     Mathlib give (`SmoothPartitionOfUnity`, `exists_isSubordinate` on a manifold with corners; is there a
     usable global change-of-variables theorem for a smooth map that is a diffeo off a null set)? Rank
     (ii-a)/(ii-b)/(ii-c) by value per unit of work. Which does the paper actually need for its Theorem
     (eq:expectation_intro_asymp / thm:expectation_expansion)?
 (iii) The multi-chart, multi-point coefficient formula: `c = ∑_{i,k} c_{i,k}` where `c_{i,k}` is the
     tied-face coefficient of the box `(i,k)` with the amplitude factor `χ_{i,k} · (weight)`. In (ii-b)
     the weight is `1`. Is the resulting `c` "intrinsic" in any provable sense (independent of the choice
     of boxes and `χ`)? Uniqueness of the leading coefficient (`HasLeadingTerm.pair_unique` — two
     certificates of the same function agree) gives independence for free once both are certificates of
     the same integral. Confirm that this is all that is needed.

**Q3 (unit sequence).** Propose the ranked unit sequence (5–7 units) for the programme, with the
statement of the main theorem of each, e.g.:
 1. `LeadingTermNegligible`: `HasLeadingTerm.add_isLittleO`, exponential-remainder wrapper, and
    "K ≥ κ on a compact set away from the zero set ⇒ the Boltzmann integral over it is `≤ C e^{−κN}`".
 2. `SourceAmplitudePackage`: the χ-weighted one-chart package/theorem (Q1b).
 3. `SourceBoxPartition`: within one chart, the finite box cover of the divisor locus + continuous
    source partition of unity from Mathlib, and the exact decomposition with exponentially small remainder.
 4. `OneChartExplicitCoefficient`: for ONE monomial chart, `∫_{φ(dom)} F p e^{−NK} ~ c N^{−λ*} log^{k*}`
    with `c = ∑_k c_k > 0` explicit — the coefficient of the WHOLE chart image (upgrading CCLXXI from a box
    to the chart), `(λ*, k*)` the extremal divisor pair over the divisor points of the chart.
 5. `DisjointChartAssembly` (ii-b) and/or `CompatibleResolution` (ii-c).
 6. `ResolutionExplicitCoefficient`: for analytic `K ≥ 0` near a zero `w`, `F, p > 0`: some compact
    neighbourhood has `∫ F p e^{−NK} ~ c N^{−λ*} log^{m*−1}` with `c > 0` EXPLICIT — the small-ball
    version of CCVIII/CCIX with the constant (this needs the a.e.-disjointness or compatibility input:
    say honestly whether it is reachable from hironaka's interface at all, or only as a conditional).
 7. A regression: e.g. `K = x² + y²` via the two blow-up charts `(s,t) ↦ (s, st)` and `(s,t) ↦ (st, t)`
    (their images overlap on the wedges; the counting weights are NOT continuous) — does (ii-b) apply after
    clipping to the two wedges `|b| ≤ |a|`, `|a| ≤ |b|` (a.e. disjoint, boundary null)? That would be a
    genuine multi-chart, non-identity-chart test with `λ = 1`, `m = 1`, `c = π` (the Gaussian).
Correct my statements, remove what is unprovable, and add anything under-served in §3–§4 of the paper
that this programme should absorb (subleading terms remain declared out of scope unless you argue
otherwise).

**Q4 (Mathlib).** Name the Mathlib lemmas you expect to carry the source partition of unity on a compact
subset of `Fin d → ℝ` (finite open cover of a compact set → continuous `χ_k ≥ 0`, `supp χ_k ⊆ O_k`,
`∑χ_k = 1` on the compact set), the change of variables for a `C¹` map injective off a null set with
nonvanishing Jacobian off the null set (`integral_image_eq_integral_abs_det_fderiv_smul` needs `InjOn` on
the set and `HasFDerivWithinAt` on the set — how do we handle the null set `E` where injectivity fails:
restrict to `dom \ E`, which is measurable, and use `volume E = 0`?), and the uniform positivity
`K∘φ ≥ κ` on a compact set disjoint from the zero set (`IsCompact.exists_isMinOn` +
continuity). Flag any that you believe do NOT exist in current Mathlib so I grep first.
