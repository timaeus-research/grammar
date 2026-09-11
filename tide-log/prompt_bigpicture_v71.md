# Astra consult #71 — routes (C) and (D) landed; the resolution formula for the exponent; last gap

Lean 4 / Mathlib formalisation `timaeus-research/grammar` (namespace `Grammar`, 511 modules, no
sorry, axiom-clean). Since consult #70 (route C first, then D):

## 1. Landed (all axiom-clean)

* **CCV `ChartLeadingTerm`** (route C): general box side via the exact scaling law of `boxCoeff`
  (`dataBoxCoeff … b x λ (m−1) = b^{Σh+n+1}(b^{2Σk})^{−λ}·amplitudeCoeff`, vanishing above `m−1`);
  uniform analytic core decompositions: `gCoeff_{λ,m−1} = Σ_I (scaled face integrals)`,
  `isEquivalent_uniform` via the first-nonzero theorem. `IsMonomialChart.local_leading_term`: at a
  divisor point with `F(φ y₀) > 0`, `∫_Ω F e^{−NK} ~ c N^{−λ}(log N)^{m−1}`, `c > 0`,
  `λ = min_j (h_{n_j}+1)/(2k_j)`, `m = #minimisers`, and `c` explicit:
  `c = Σ_s b'^{Σh+n+1}(b'^{2Σk})^{−λ} ∫_{A'} Γ(λ)β^{−λ}/(m−1)! ∏_{j∈M}(2k_j)^{−1}
  ∫_{[0,1]^{n+1}} amp_s(v, b'π_M u) ∏_{j∉M} u_j^{h_j−2k_jλ} du dv` with `amp_s = jac_s·F∘Ψ_s`
  the fully transformed orthant amplitude — your §2 normalisation (including the two-sided
  `2/a_j` through the orthant sum).
* **CCVI `GlobalExponentBound`** (route D): abstract Θ-theorem from finitely many local leading
  terms with an a.e. phase gap off their union (overlaps allowed; lower bound one piece, upper
  bound Σ pieces + `e^{−Nδ₀}∫F`), and `freeEnergy_asymptotic`:
  `−log Z = λ_* log N − (m_*−1) log log N + O(1)`.
* **CCVII `GlobalExponentHironaka`**: THE FINITE COVER EXISTS for a hironaka `PartialResolution`
  (your §1.2 said it was unavailable — it is available): the divisor-point region contains the
  chart image of an OPEN source neighbourhood of `y₀` (the strip box contains an open coordinate
  box, whose inverse image under the strip normalisation `T` is open, and `T⁻¹0 = 0`); the chart
  domains are compact; `PartialResolution.cover : volume (N \ ⋃ φ_i(dom_i)) = 0` and
  `mapsTo : φ_i(dom_i) ⊆ N`. Covering each compact `dom_i ∩ φ_i⁻¹(B̄(w,r))` by finitely many
  divisor-point neighbourhoods and by neighbourhoods with `K∘φ_i ≥ K(φ_i y₀)/2 > 0` gives the
  pieces and the gap `δ₀`. Theorem `exponent_of_monomialResolution`: for `K ≥ 0` analytic on open
  `U ∋ w`, `K w = 0`, `F > 0` analytic on `U`, `N` a compact neighbourhood of `w`, and
  `R : PartialResolution d K N` whose charts are `IsMonomialChart K (φ_i) (dom_i) e_i h_i W_i`
  with **`∀ j, 0 < h_i j → 0 < e_i j`**: there is a compact neighbourhood `Ω ⊆ U` of `w` and a
  finite family of divisor-point chart pairs `(λ_p, m_p) = (C_p.lam, C_p.mult)` with
  `∫_Ω F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})`, `λ_* = min λ_p`, `m_* = max{m_p : λ_p = λ_*}`.
  I.e. the resolution formula for the exponent pair (min over divisor points of the charts of the
  minimal Mellin ratio of the normal exponents), at the level of the Laplace integral.

## 2. The one remaining hypothesis: `∀ j, 0 < h j → 0 < e j`

hironaka's `IsMonomialChart` (`K∘φ = u y^e`, `det Dφ = v y^h`, `InjOn φ {y^h ≠ 0}`) relates `h`
and `e` in no way, and `Q_all`'s readout does not record that the Jacobian divisor lies inside the
phase divisor (true for BM89's algorithm: centres in the zero set). So the corollary through
`exists_monomialResolution_at (Q_all d)` is not stated. Where the hypothesis is used: at a
divisor point `y₀`, the normal set is `S = {j | y₀_j = 0 ∧ e_j > 0}`; a coordinate `j ∉ S` with
`y₀_j = 0` and `h_j > 0` contributes `|y_j|^{h_j}` to the Jacobian while the phase does not
involve `y_j`; the current centred normal form absorbs tangential Jacobian factors into an
analytic positive unit, which needs `h_j = 0` there. Also `φ` is then not injective on the
hyperplane `{y_j = 0}` (only off `{y^h ≠ 0}`), so the orthant split box charts are injective only
off a null set of the box.

My plan to remove it (weighted tangential coordinates):
(a) `SplitBoxChart.injOn` → injective off a measurable null set `N₀` of the box; the core
    presentation then uses the change of variables on `box \ N₀` and `Ψ(box ∩ N₀)` null (C¹ image
    of a null set); `CorePiece.measurableSet_image` → `NullMeasurableSet`, with `toMeasurable` in
    the core decomposition.
(b) `CentredChartData` gains tangential weights `hT : Fin t → ℕ` (`hT i = h_{t_i}` if `y₀_{t_i}=0`,
    else absorbed): `|det Dφ(y+y₀)| = jac₀(y) ∏_j |y_{n_j}|^{h_{n_j}} ∏_i |y_{t_i}|^{hT_i}`, and
    `y^h ≠ 0` off the normal AND weight hyperplanes.
(c) Orthant chart: `jac := jac₀·ρ^{−h}·|det DT⁻¹|·∏_i |v_i|^{hT_i}` (the strip normalisation fixes
    tangential coordinates, so the weight is a function of the tangential variable `v` only),
    `amp v := w(v) • jointDatum(v)` with `w(v) = ∏|v_i|^{hT_i}` continuous (scalar multiplication
    in the ℓ¹ data space; `evalF` linear), injectivity off the weight hyperplanes.
(d) Leading term: face functionals `≥ 0` on the box, `> 0` off the weight hyperplanes ⇒ the
    tangential integral is positive (support of positive measure); exponents unchanged (the
    weights carry no phase): `λ, m` from `S` only.
(e) Then `exponent_of_monomialResolution` without the hypothesis, and the corollary through
    `Q_all`: an unconditional resolution formula for the exponent of `∫ F e^{−NK}`.

## 3. Ask

1. Is the weighted-coordinate plan mathematically right — in particular (d): the tangential
   weight `∏|v_i|^{hT_i}` does not change `(λ, m)` and the face integral stays positive? Any
   hazard with the a.e.-injectivity change of variables (Ψ C¹ on an open neighbourhood of the
   closed box, injective off finitely many hyperplanes)?
2. Is there a cheaper way to discharge `0 < h j → 0 < e j` — e.g. is it a consequence of
   `IsMonomialChart` + `K ≥ 0` + `K(φ y₀) = 0` at the relevant points that I am missing, or a
   property one can extract from the readout (`IsQChart`/`PartialResolution.E`) without
   modifying hironaka? (We do not modify hironaka; anything on top is built in grammar.)
3. After (e): what is the paper-relevant next target? Options: (i) the full power–log EXPANSION
   over the region — blocked by the cross-chart gate (your §4); (ii) `λ_*` is independent of the
   chosen finite subcover / equals the min over ALL divisor points of the resolution (uniqueness of
   the exponent pair, `powerLogRate_pair_eq_of_isTheta_nat` exists); (iii) identify `λ_*` with
   hironaka's own `(λ_H, θ_H)` of `laplaceTheta` (CLXXXV) — gives "the RLCT of K at w is the
   resolution formula"; (iv) the empirical/annealed transfer of the identified pair (the paper's
   Section on the fluctuation of `log Z_n`); (v) something else.
4. Anything in §1 over-claimed. Be blunt.
