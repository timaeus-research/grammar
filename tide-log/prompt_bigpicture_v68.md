# Astra consult #68 — the compatible divisor localisation gate after units 1–2

You are advising the Lean 4 / Mathlib formalisation `timaeus-research/grammar` (namespace `Grammar`,
491 modules, no sorry, axiom-clean) of Gerraty–Murfet, *Grammar (Expectations and the Exceptional
Divisor)*. Your consult #67 laid out an eight-unit programme for the geometric bridge on top of the
completed `timaeus-research/hironaka` chart form (`Monomialize.Analytic.Q_all`), with unit 4
(`CompatibleDivisorLocalisation`) as the critical research gate. Units 1 and 2 have landed. I need a
decision on how to attack unit 4, based on what the hironaka readout actually provides and on an
analysis below that simplifies units 3, 5 and 7 considerably. Be blunt and specific; say which of my
claims are wrong.

## 1. What landed

**Unit 1 (`AnalyticCorePresentation.lean`).** `CorePresentation D target K n β`: base measure `ν`
on compact `K`, exponents `h k`, box side `b`, chart `Φ : K × (Fin (n+1) → ℝ) → U`, density `c`,
tangential datum `x : C(K, DataSpace (n+1))` (ℓ¹ coefficient families), with
`transport : ((ν ⊗ vol|_{(0,b]^{n+1}}).withDensity (u^h c)).map Φ = target`,
`phase_normal : K(Φ(v,u)) = β ∏ u_i^{2k_i}` a.e., `amplitude_eq : evalF (toEta b (x v)) u = c(v,u) · F(Φ(v,u))` a.e.
(so `c · F∘Φ` must be the absolutely convergent power series `∑_γ x_γ (u/b)^γ` on the whole box),
`fluct_zero`. `AnalyticCoreDecomposition D M K n β`: `D.μ = ∑_I core_I + tail`, a core presentation
of each `core_I`, and `δ₀ ≤ phase` a.e. on `tail`; from it the population expansion theorems follow
verbatim. `HasAnalyticCoreDecomposition D β` and the target proposition
`CompatibleDivisorLocalisation d` (for every real-analytic `K ≥ 0` at a zero where it is not
identically zero and every observable, all small closed cubes admit a decomposition). I now believe
the observable there must be real-analytic, not merely continuous (the amplitude clause forces it);
I will correct that.

**Unit 2 (`MonomialUnitRemoval.lean`).** On a monomial chart `K = u · y^e` with analytic `u > 0`:
`rescale i r y := update y i (y_i · r y)`, `unitRoot β m u := exp(log(u/β)/m)`;
`exact_normal_form : K y = β · monomialEval (rescale i (unitRoot β (e i) u) y) e`;
`analyticAt_rescale`, `hasFDerivAt_rescale_of_zero` (differential `diag(1,…,(u/β)^{1/e_i},…,1)` at
centres on `y_i = 0`), and via `HasStrictFDerivAt.toOpenPartialHomeomorph` +
`OpenPartialHomeomorph.hasFPowerSeriesAt_symm` a `LocalNormalForm K β e W y₀` (analytic local
homeomorphism `ψ` with analytic inverse at the centre, `K = β (ψ y)^e` on the source, `K ∘ ψ⁻¹ = β z^e`
on the target). Positivity of `u` and of `e_i` are hypotheses; parity/sign from `K ≥ 0` is the next
small unit.

## 2. What the hironaka readout provides (inspected, not assumed)

`exists_monomialResolution_at : Q n → … → ∃ N, IsCompact N ∧ N ∈ 𝓝 w ∧ ∃ R : PartialResolution n K N, R.IsMonomial`.

`PartialResolution n F K` fields: `ι` finite; `dom i` compact; `φ i` smooth on an open nbhd of
`dom i`; `mapsTo : MapsTo (φ i) (dom i) K`; **`cover : volume (K \ ⋃ i, φ i '' dom i) = 0`** (cover
up to a null set only); `E i ⊆ dom i` closed null with `InjOn (φ i) (dom i \ E i)` and nonvanishing
Jacobian off `E i`; a multiplicity bound `mult` off a null set. `IsMonomial`: each chart has
`IsMonomialChart K (φ i) (dom i) e h W` — `W ⊇ dom i` open, `φ` analytic on `W`, injective on
`{y ∈ W ∧ y^h ≠ 0}`, `K ∘ φ = u · y^e` on `W` with `u` continuous nonvanishing (upgraded to analytic by
`analyticOnNhd_of_eq_continuousOn_mul_monomial`), `det Dφ = v · y^h`.

Internally each chart is an `IsQChart`: `φ = π ∘ ψ` with `π` an `IsAdmissibleComposite` — a
**per-chart** composite of moves (`blowUpChart` of a coordinate subspace, analytic `shear`, translate,
linear) — and `ψ` an analytic local isomorphism, injective on `W`, onto part of the final data's open
set. There is no common manifold, no transition map between different charts, and `cover` is only
a.e. The `PartialResolution` is built by refinement (a chart refined by a partial resolution of the
pulled-back function), so charts are leaves of a refinement tree; the readout forgets the tree.

## 3. My analysis — please check each claim

**(A) A box with an exact monomial phase is a single core.** Once `K = β ∏_{j∈J} z_j^{2k_j}` exactly
on a product box `A × [-r,r]^J` in analytic coordinates `z` (A the tangential box), the whole box is
one exact core with `n+1 = |J|` normal coordinates: the 2^{|J|} orthants map to `(0,b]^J` by sign
reflections (even exponents), `ν = vol_A ⊗ counting`, `Φ(v,σ,u) = φ(T⁻¹(v,σu))`, and the sub-strata
`z_j = 0, j ∈ J' ⊊ J` inside the box need **no separate treatment** — the box theorem's exponent
lattice `Λ(h,k)` already accounts for every face. Unit 5 ("coordinate-adapted partition") is needed
only to reach the parts of the chart domain *outside* such a box.

**(B) The unit-removal map is global on the chart, injective by one-variable monotonicity.**
`T(y) = update y i₀ (y_{i₀} ρ(y))`, `ρ = (u/β)^{1/2k_{i₀}}`, is one analytic map on the whole chart
domain; for fixed other coordinates `y_{i₀} ↦ y_{i₀} ρ(y)` is strictly increasing on `|y_{i₀}| ≤ b₀`
where `ρ + y_{i₀} ∂_{i₀}ρ > 0` (compactness), so `T` is injective on `Q₀ = {y ∈ Q : |y_{i₀}| ≤ b₀}` and
`T(Q₀) ⊇ Q' × [-b₀ρ_min, b₀ρ_min]` — the z-box has full extent in every coordinate but `i₀`. No IFT
is needed for injectivity; the analytic inverse is local (unit 2). The Jacobian of `φ ∘ T⁻¹` is
`|z^h| · [ |v| ρ^{-h_{i₀}} / (ρ + y_{i₀}∂ρ) ]∘T⁻¹`, i.e. `u^h ×` an analytic positive unit.

**(C) Inside an exact-monomial box, the region outside the deep sub-box tiles exactly into
product cores with monomial units.** With phase `β∏_{j∈J} u_j^{2k_j}` on `[-r,r]^J` and a small `b`:
the deep core `[-b,b]^J`; for a point with `S(u) = {j : |u_j| ≤ b} ≠ ∅, J` the unit on the stratum `S`
is the monomial `β∏_{i∉S} u_i^{2k_i}` in the *tangential* coordinates, so the rescaling
`w_{i₁} = u_{i₁} ∏_{i∉S} |u_i|^{k_i/k_{i₁}}` depends only on tangential coordinates, has Jacobian
equal to that monomial (independent of `u_{i₁}`), and the core
`C_S = {|u_i| > b (i∉S)} × {|u_j| ≤ b (j ∈ S∖i₁)} × {|w_{i₁}| ≤ b_S}` with `b_S = b^{1+∑_{i∉S}k_i/k_{i₁}}`
is a product in the coordinates (tangential, normal). The leftover `{b_S/∏ < |u_{i₁}| ≤ b}` is
**not** gapped when `|S| ≥ 2` (phase `β w_{i₁}^{2k_{i₁}} ∏_{S∖i₁} u_j^{2k_j}`), so it is passed to the
stratum `S∖{i₁}` whose tangential set then includes it (tangential sets may be arbitrary compact sets,
on which the monomial unit is bounded below); when `|S| = 1` the leftover has phase `> β b_S^{2k}` and
is tail; `S = ∅` has phase `≥ β b^{2∑k}`. Processing strata by decreasing `|S|` gives a finite
measurable tiling of the box into product cores (with one monomial rescaling each) plus a gapped
tail. In log-coordinates `log|u_j|^{k_j}` every core is a polyhedron and the phase is linear. This
replaces the paper's adapted partition of unity (`lem:adapted_pou`, whose "constant on normal
fibres" construction is not correct as written) by an exact tiling, with no smooth cutoff at all.
Amplitudes: every core's amplitude is analytic in its normal coordinates near the compact closed
box; with `b` below the uniform radius at divisor points all power series converge on their boxes
(`b` is the one global smallness parameter).

**(D) The region `|y_{i₀}| > b₀` of a chart, where `T` is not injective,** needs a second rescaled
coordinate `i₁ ≠ i₀` with unit `u · y_{i₀}^{2k_{i₀}}`; its wall against the `z`-box must be matched.
The wall of the `z`-box is `{|z_{i₀}| = b}` — a level set of the analytic function `z_{i₀} = y_{i₀}ρ(y)`
which depends on the normal coordinates of the stratum `J∖{i₀}`. I believe the matching is possible
by the **freedom of tangential coordinates**: a core for stratum `S` may use any analytic tangential
coordinates whose level sets are transverse to the divisor (the phase and Jacobian clauses only
constrain the normal coordinates), so the neighbouring core can take `z_{i₀}` itself as a tangential
coordinate on `{b ≤ |z_{i₀}|, |y_{i₀}| ≤ b₀}`. Is this right, and is it worth the complexity, or
should the `y_{i₀}`-extent of the chart box simply be taken ≤ `b₀` (shrinking the chart domain in one
direction, which is harmless if a *finite cover by such boxes* is what we assemble anyway)?

**(E) The cross-chart problem is exactly the wall-matching problem across charts, and the readout
does not supply the data.** Two charts' saturated pieces `φ_1(A_1 × box)`, `φ_2(A_2 × box)` overlap
near the zero set; for a tiling, the common boundary must be a wall saturated in *both* charts, i.e.
chart 2's tangential coordinates must have a level set equal to chart 1's wall `φ_1(H × box)`. By
(D)'s freedom this is possible **if** that wall is, in chart 2's coordinates, an analytic hypersurface
transverse to chart 2's divisor — which needs the transition `φ_2⁻¹∘φ_1` to extend analytically across
the divisor. The readout gives no transition maps at all (your #67 warning), only `InjOn` off `E` and
a null-set cover. So from the readout alone, unit 4 is not provable as stated; a genuine analytic
tiling of a neighbourhood of `K⁻¹(0)` by chart boxes is an additional geometric input.

## 4. The decision I need

1. Confirm or refute (A)–(E). In particular (A) and (C): is the exact tiling a faithful and
   *complete* replacement of `lem:adapted_pou` for the paper's theorem, and does (A) really make the
   sub-strata inside a deep box free?
2. Given (E), which of these do you recommend, and why:
   (i) **Interface route**: define `DivisorAdaptedTiling d K N` — finitely many monomial chart
   boxes (analytic on a nbhd, injective, `K∘φ = u y^{2k}`, `det = v y^h`) whose images are pairwise
   disjoint up to null sets and whose union contains `N ∩ {K < δ₀}` up to a null set — prove
   `HasAnalyticCoreDecomposition` from it via (A)–(C) and unit 6, and state its inhabitance as the
   one remaining geometric proposition with a precise contract. Your #67 stop rule says "a structure
   with an unproved inhabitance theorem is not completion"; is this nevertheless the right next
   deliverable, since it isolates the exact geometric obligation?
   (ii) **Hironaka-internals route**: recover from hironaka's Q induction (per-chart composites of
   `blowUpChart`/shear/translate/linear moves and the refinement tree) a stronger readout in which
   sibling charts of one blow-up are the standard affine charts with monomial transitions, so that a
   tiling by unit boxes in the slope coordinates exists (the two charts of a point blow-up in ℝ² with
   `|slope| ≤ 1` tile exactly). Is this true of the BM89 construction as formalised (maximal contact,
   shears), or do shears and the a.e. cover destroy it? Estimate the size of this recovery honestly.
   (iii) Something else: e.g. a tiling of the *target* built from the phase and the finitely many
   charts directly, a signed decomposition, or an argument that the population expansion does not
   actually need exact tiling (I do not see one: any non-saturated transition region touching the
   zero set contributes power-law terms).
3. Sizing: (C) in general `|J|` is a finite recursion over subsets with explicit monomial maps; I
   estimate 1500–2500 Lean lines. Is there a slicker formulation (e.g. the polyhedral/log picture,
   or a single "greedy" assignment `S(u)` with rescaling of the *largest-normalised* coordinate) that
   avoids the leftover recursion?
4. Unit 6 (real-analytic → ℓ¹ tangential datum): from `HasFPowerSeriesOnBall g(v,·) p_v 0 R` with
   `R > b` on the sup-norm cube, I plan monomial coefficients
   `c_γ(v) = ∑_{r : Fin |γ| → Fin d, mult(r) = γ} p_{|γ|}(e∘r)`, ℓ¹ bound via
   `norm_mul_pow_le_of_lt_radius` and the polynomial count of `r` with given multiplicity, and
   `evalF = g` by `MultilinearMap.map_sum_finset` and regrouping. Continuity in `v` from joint
   analyticity. Any Mathlib shortcut (e.g. `FormalMultilinearSeries` ↔ `MvPowerSeries`,
   `HasFPowerSeriesOnBall.coeff`-style API for `Fin d → ℝ`) I should know about, and any trap?
5. Order of work for the next 3–4 units, with stop rules, under the owner's directive that all
   material on top of hironaka is developed in grammar.
