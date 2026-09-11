# Astra consult #70 — the local chart theorem is unconditional; what is the global step?

Lean 4 / Mathlib formalisation `timaeus-research/grammar` (namespace `Grammar`, 508 modules, no
sorry, axiom-clean) of Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*. Your
consults #68/#69 fixed the route (strip normalisation → exact-monomial boxes → ℓ¹ amplitudes →
conditional tiling bridge; B0/B1 as unconditional endpoints; cross-chart gate as a research
proposition). Everything from #69 has landed and I went one level further: the single-chart theorem
is now stated for the hironaka chart itself, at every divisor point, unconditionally. I need the
next decision. Be blunt; say which claims are wrong.

## 1. Landed since #69 (all axiom-clean, `#print axioms` = propext/choice/Quot.sound)

* **B0 (CXCV–CXCVI)**: exact-monomial phase `β∏u_j^{2k_j}` on `A×[0,b]^{n+1}` and on the two-sided
  box `A×[-b,b]^{n+1}` (2^{n+1} reflected pieces, `|det R|=1`, joint reflection is a linear isometry
  so the series margin `(t+n+1)B<ρ<R` is preserved): full power–log cutoff expansion with the
  observable given by ONE joint power series.
* **B1 (CXCVII–CXCVIII)**: phase `unit·∏y_{n_j}^{2k_j}` with analytic positive `unit`; strip
  normalisation `T`; change of variables to the two-sided box with amplitude `|det DT⁻¹|·F∘T⁻¹`,
  which is jointly analytic (`det DT⁻¹ = (ρ + y_i∂_iρ)⁻¹`); shrinking base and normal side below
  the radius gives the expansion of `∫_{T⁻¹(A'×[-b',b']^{n+1})} F e^{-NK}` with no series hypothesis.
* **CXCIX `AnalyticJacobian`**: the continuous units of an `IsMonomialChart` are analytic
  (quotient by the monomial off the divisor + hironaka's removable-factor lemma
  `analyticOnNhd_of_eq_continuousOn_mul_monomial`); `det ∘ fderiv` of an analytic map is analytic.
* **CC `SplitBoxCore`**: `SplitBoxChart σ D A b β` = C¹ endomorphism `Ψ` of `Fin d → ℝ`, injective
  on the positive box `prodToPi σ (A×(0,b]^{n+1})` along a coordinate splitting
  `σ : Fin t ⊕ Fin (n+1) ≃ Fin d`, `|det DΨ| = ∏u^h · jac`, exact phase, amplitude datum
  ⇒ `CorePresentation` of `vol|_{Ψ(box)}`. Abstract `CorePiece`/`CoreTiling` (region `Ω`,
  finitely many pieces inside, pairwise a.e.-disjoint images, phase gap a.e. off the union) ⇒
  `HasAnalyticCoreDecomposition` ⇒ `CoreTiling.cutoffExpansion`.
* **CCI `SplitReflection`**: reflections `R_s` of the normal coordinates in `Fin d → ℝ`;
  orthants disjoint; a.e. coverage of the two-sided box by the 2^{n+1} orthants.
* **CCII `CentredChart`**: at a divisor point `y₀` of `IsMonomialChart K φ dom e h W` with `K ≥ 0`
  analytic on open `U ∋ φ y₀`, `K(φ y₀)=0`, `∀ j, 0<h_j → 0<e_j`: `CentredChartData` — splitting
  into the normal set `{j | y₀_j=0 ∧ e_j>0}` (nonempty) and tangential coordinates, even normal
  exponents `e_{n_j}=2k_j`, and in translated coordinates `K(φ(y+y₀)) = unit₀(y)∏y_{n_j}^{2k_j}`,
  `|det Dφ(y+y₀)| = jac₀(y)∏|y_{n_j}|^{h_{n_j}}` with analytic positive `unit₀, jac₀` on an open
  `V₀ ∋ 0`; the Jacobian monomial is nonzero off the normal hyperplanes (⇒ `φ` injective there).
* **CCIII `ChartOrthantCore`**: the orthant charts `Ψ_s = φ(T⁻¹(R_s ·)+y₀)` are `SplitBoxChart`s:
  chain-rule Jacobian `|det DΨ_s| = ∏u_j^{h_{n_j}} · jac₀ · ρ^{-h_{n_{j₀}}} · |det DT⁻¹|`
  (`∏|w_{n_j}|^{e_j} = (∏|z_{n_j}|^{e_j})ρ(w)^{-e_{j₀}}` for `Tw=z`), exact phase, injective on the
  box (`T⁻¹` preserves nonvanishing of coordinates), amplitude from the joint series.
* **CCIV `ChartOrthantTiling`** — THE LOCAL CHART THEOREM:
  `IsMonomialChart.local_cutoffExpansion (hc : IsMonomialChart K φ dom e h W) (hU : IsOpen U)
  (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
  (hhe : ∀ j, 0 < h j → 0 < e j) (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0)
  (hF : AnalyticOnNhd ℝ F U) : ∃ Ω, IsCompact Ω ∧ φ y₀ ∈ Ω ∧ Ω ⊆ φ '' W ∧ Ω ⊆ U ∧
  ∃ Q Dg c, 0 < Q ∧ CutoffExpansion Q Dg (fun N => ∫ x in Ω, F x * exp(-N K x)) c`.
  Proof: the 2^{n+1} orthant charts tile `Ω = g(A'×[-b',b']^{n+1})` under the strip chart
  `g = φ(T⁻¹(·)+y₀)`: `g` injective off the normal hyperplanes ⇒ disjoint images; the missed part of
  `Ω` is `g(zBox ∩ {some normal coord = 0})`, null as the image of a null set under a differentiable
  map (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`); series of every orthant
  amplitude at the origin, common margin below the minimum of the 2^{n+1} radii ⇒ `CoreTiling`.

Honest non-claims: `Ω` is the chart's own strip box image — NOT a neighbourhood of `φ y₀` in the
ambient space (at a divisor point `φ` is not a local diffeo; `φ(W)` near `φ y₀` is what it is).
One divisor point of one chart. The hironaka audit (#69) stands: `Q_all` outputs a finite family of
independent `IsMonomialChart`s with common target, a.e. coverage `volume (K \ ⋃ φ_i(dom_i)) = 0`,
chartwise injectivity off the divisor, a summed/multiplied multiplicity bound, no transition data,
no ownership/partition of the target.

## 2. What the paper needs and where the gap is

`thm:expectation_expansion` is the expansion of `∫_{K≤δ} F e^{-NK}` over a compact region of the
ambient parameter space (or of `Z_N = ∫ e^{-NK}φ`). To get it from the charts one must write the
region (mod null) as a disjoint union of pieces each pulled back to a chart where it is a
box-tiling — the pieces of different charts must be cut along walls saturated for both charts'
normal fibres (or the overlaps must themselves be box-tileable). Nothing in `Q_all` provides this.

Three candidate routes I can see; I want your ranking or a fourth:

(A) **Measurable ownership + inclusion–exclusion on the chart side.** Cover the compact region by
finitely many local `Ω_i` (from CCIV at divisor points) plus a set where `K ≥ δ₀`. The overlaps
`Ω_i ∩ Ω_j` are not boxes in either chart; but pulled back to chart `i` they are semianalytic subsets
of the strip box. Is there a clean way to see that `∫_{Ω_i∩Ω_j} F e^{-NK}` still has a power–log
expansion (e.g. because `Ω_i ∩ Ω_j` in chart-`i` coordinates is `T⁻¹(box) ∩ φ_i⁻¹(Ω_j)` and
`φ_i⁻¹(Ω_j)` is itself a finite union of images of boxes under analytic maps in the SAME chart
coordinates)? If every finite intersection has an expansion, inclusion–exclusion gives the
expansion of the union. This needs: expansions for `∫_{Ω} F e^{-NK}` over regions `Ω` that are
images of boxes under *several* analytic maps — i.e. a "several strip charts in one hironaka chart"
statement. Is that any easier than the cross-chart gate?

(B) **Fibre-saturated partition inside one chart.** Develop in grammar: for finitely many
`IsMonomialChart`s covering a compact region a.e., choose a measurable partition `P_i ⊆ φ_i(W_i^{off})`
and show each `φ_i⁻¹(P_i)` can be tiled by cores. The cores need a product structure
(tangential base × normal box); an arbitrary measurable `P_i` destroys it. The exact-monomial
tiling (CXC) works for *any* `S`-cylindrical measurable base `B`, so the requirement is only that
the walls be saturated for the normal fibres of chart `i`. Is there a natural choice of partition
(e.g. by "which chart has the largest Jacobian monomial" or a Voronoi-type rule in a common metric)
whose walls are saturated? I doubt it — the normal fibres of different charts are transverse in
general — so I suspect (B) is exactly the research gate. Confirm or refute.

(C) **Change the target statement.** Accept the chart-level theorem as the geometric main theorem
of the paper's Lean mirror and turn to identifying the *exponent* of the local expansion: the
leading power–log pair of `∫_Ω F e^{-NK}` from the normal exponents `(h_{n_j}, k_j)` — the
lattice minimum `λ = min_j (h_{n_j}+1)/(2k_j)`, multiplicity = number of minimisers — and the
leading coefficient in terms of the face integral of `jac₀·F∘φ` over the tangential base (the
paper's `c_λ` formula). Do we already have enough machinery (`cutoffExpansion_of_hasAnalyticCore
Decomposition` assembles canonical coefficients; CLXXXV gives the exponent pair for the SUMMED chart
form) or does the identification need new theorems? Which is the *paper-relevant* payoff: the
global expansion with an unidentified exponent, or the local one with identified exponent?

(D) Something else you see.

## 3. Constraints (unchanged)

hironaka is consumed only through axiom-clean declarations (`IsMonomialChart`,
`analyticOnNhd_of_eq_continuousOn_mul_monomial`, the readout `exists_monomialResolution_at` /
`PartialResolution` fields if needed); we do NOT use hironaka's E6; anything on top of hironaka we
develop in grammar. Statements only on bounded precise claims; non-claims stated.

## 4. Ask

1. Rank (A)/(B)/(C)/(D) by expected value for the paper's Lean mirror in the next ~10 units; say
   which is a research gate versus engineering.
2. For your top choice, give the precise Lean-level statements of the first three units (types of
   the hypotheses and conclusions), the Mathlib lemmas to lean on, and the hazards.
3. If (A): is "several analytic images of boxes in one chart, with intersections" tractable — is
   there a theorem in the literature (Hironaka's rectilinearisation / Łojasiewicz's semianalytic
   partitions) that one would be re-proving, and is its bounded version accessible?
4. For (C): the exact statement of the identified leading term you would stand behind
   (normalisations included), and whether the multiplicity is the count of lattice minimisers or
   the maximal face dimension.
5. Anything in §1 you think is wrong or over-claimed.
