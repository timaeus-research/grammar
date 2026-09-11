# Astra consult #69 — after the conditional bridge: the inhabitance endpoint

Lean 4 / Mathlib formalisation `timaeus-research/grammar` (namespace `Grammar`, 498 modules, no
sorry, axiom-clean) of Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*. Your
consult #68 fixed the route: local strip normalisation → exact-monomial rectangular extraction → ℓ¹
amplitudes → conditional tiling bridge, with the cross-chart gate left as the research proposition.
All of it has landed since; I need the next decision. Be blunt; say which claims are wrong.

## 1. Landed since #68 (all axiom-clean)

* **CLXXXVIII `MonomialParity`**: on `K = u·y^e ≥ 0` (open `W`, `u` continuous nonzero at `y₀`) every
  coordinate vanishing at `y₀` has an even exponent (sign-flip probe); reduced form
  `K = u'·∏ y_j^{2k_j}` with `u' > 0` analytic near `y₀`, `k` supported on `{y₀_j = 0}`.
* **CLXXXIX `StripNormalisation`**: `T = rescale i ρ` is injective on an open strip over a compact
  base `Q₀ ⊆ {y_i = 0}` by fibrewise monotonicity (no IFT), Jacobian `ρ + y_i∂_iρ > 0`
  (`det_rescaleDerivAt`), image open and ⊇ a cylinder of positive height, `invFunOn` analytic on
  the image.
* **CXC `MonomialTiling`**: exactly your weighted-product invariant. `MonomialCore` = (stratum `S`,
  rescaled coordinate `i ∈ S`, `S`-cylindrical measurable base `B`, `qmin`), core set
  `B ∩ {|u_j| ≤ b (j ≠ i), |u_i| q_S^{1/k_i} ≤ b·qmin^{1/k_i}}`, phase exactly `∏_{j∈S} w_j^{2k_j}`
  in the rescaled coordinates. `exists_absorption` (induction on `|S|`, invariant `q_S ≥ qmin`) and
  `exists_monomialTiling`: the box `[-r,r]^m` = finitely many good cores, pairwise disjoint, plus a
  set with phase `≥ δ > 0`. Initial split by `T = {|u_j| > b}`.
* **CXCI `MonomialCoefficients`**: monomial coefficients of a `FormalMultilinearSeries` on `ι → ℝ` by
  words/multiplicities; `∑_{|γ|=n}|c_γ| ≤ (card ι)^n‖p n‖`; ℓ¹ summability for `card ι·b < ρ < radius`;
  absolute convergence to `f` on the cube (`HasSum.sigma` along degrees); `amplitudeDatum` in
  `DataSpace` with `evalF (toEta b x) u = f u`.
* **CXCII `JointAmplitude`**: one joint series on `Fin t ⊕ Fin m → ℝ` ⇒ fibre families
  `jointFibre P v γ' = ∑_α C_{α,γ'} v^α`, uniform majorant `∑_α |C_{α,γ'}| B^{|α|}`, evaluation to
  `G(v,u)` on the normal box, and **ℓ¹-continuity in `v`** by dominated convergence of the joint ℓ¹
  series (`continuous_tsum`) — `jointTangentialData : C(K, DataSpace m)` over any compact `K` in the
  tangential cube. No Cauchy estimate needed, as you predicted.
* **CXCIII `PositiveBoxCore`**: `PositiveBoxChart` on `(Fin t → ℝ) × (Fin (n+1) → ℝ)` (C¹ `Ψ`
  injective on `A × (0,b]^{n+1}`, `|det DΨ| = u^h·jac`, exact phase, amplitude datum) ⇒
  `CorePresentation` of `vol|_{Ψ(A×(0,b]^{n+1})}` by `map_withDensity_abs_det_fderiv_eq_addHaar`.
* **CXCIV `ExactNormalTiling`**: `TilingPiece` (positive box chart + volume-preserving measurable
  equivalence into `Fin d → ℝ` + compact base); `LocalisationData.comapEquiv`,
  `CorePresentation.mapEquiv`; `ExactNormalTiling` (region `Ω` with `D.μ = vol|_Ω`, pieces inside `Ω`,
  pairwise a.e.-disjoint images, phase gap off the union) ⇒ `HasAnalyticCoreDecomposition` ⇒ full
  power–log cutoff expansion (`ExactNormalTiling.cutoffExpansion`). And
  `HasExactNormalTilings d → CompatibleDivisorLocalisation d`.

So the bridge theorem of route (i) is done. Everything above the interface is proved; everything
below it (inhabitance) is not.

## 2. What I see about inhabitance, and the questions

**(A) The cube endpoint is wrong-shaped.** `CompatibleDivisorLocalisation` integrates over
`closedBall w r` (sup-norm cube). The cube boundary meets the zero set `Z = K⁻¹(0)` (which is
positive-dimensional in general), and at such boundary points the cube's faces are not saturated
for the normal fibres of any chart, so a tiling piece can't be cut along them, and the boundary
region has no phase gap. (For a *product* box in normal-form coordinates with tangential walls the
cut is fine, as in the paper's own picture; for a Euclidean cube it is not.) My proposal: change the
endpoint's integration region from a cube to **a region whose boundary lies at positive phase**, or
equivalently state the theorem for a **smooth compactly supported cutoff `χ` with `K > 0` on the
support boundary**? No — `χ` smooth reintroduces non-analytic amplitude. So: `Ω` compact with
`Z ∩ Ω ⊆ interior Ω`, i.e. `K ≥ δ₁ > 0` on a neighbourhood of `∂Ω` — then the boundary shell is
tail. Is this the correct reading of the paper's integration setting (Watanabe's `W` with `K > 0` on
`∂W`), and should I restate `CompatibleDivisorLocalisation` with such an `Ω` (e.g. the sublevel set
`{K ≤ ε}` intersected with a compact neighbourhood, or `Ω` with `∂Ω ⊆ {K > 0}`)?

**(B) Single-chart inhabitance is now a finite composition.** If the low-phase part of `Ω` lies in
the image of ONE monomial chart `φ` (analytic on an open `V ⊇ dom`, injective off `{y^h = 0}`,
`K∘φ = u·y^{2k}`, `det Dφ = v·y^h`), then: parity gives `u > 0` and even exponents near each divisor
point; strip normalisation `T` puts the phase in exact monomial form on a strip over a compact base;
`exists_monomialTiling` tiles the normal box in `z = T(y)` coordinates into monomial cores; each
core is a product `(tangential set) × (normal box)` in the `coreMap` coordinates with Jacobian a
monomial times an analytic unit; the amplitude `jac·F∘φ∘T⁻¹∘coreMap⁻¹` is jointly analytic, so a
finite cover of each core's compact base by joint-series centres (with the `(t+m)·B < ρ` margin)
gives `jointTangentialData`; reflections give the other orthants. So `ExactNormalTiling` for
`Ω := φ(T⁻¹(z-box))` should be provable **in one chart** with no new ideas — only the compositions:
reindexing `Fin d ≃ S ⊕ Sᶜ` (`MeasurableEquiv.piEquivPiSubtypeProd`, volume preserving), the
Jacobian of `φ∘T⁻¹∘coreMap⁻¹` as `w^h·unit`, injectivity of the composite on the positive orthant,
covering compact bases by finitely many centres and splitting the base measure accordingly. I
estimate 3–4 units, 1500–2500 lines, mostly plumbing. **Is the single-chart theorem worth this**, as
(i) the honest unconditional endpoint for phases with a one-chart monomialisation (e.g. normal
crossings `K = ∏ y_j^{2k_j}·u` directly, the paper's `N(x₀x₁,1)` example, all products of
coordinate powers), and (ii) the reduction of the general case to *exactly* the cross-chart
tiling? Or is there a cheaper route to the same (e.g. state the single-chart theorem for the
exact-monomial phase `β∏ y^{2k}` on a product box directly — that skips strip normalisation and the
unit but is still "one chart")?

**(C) The cross-chart gate.** Two ideas since #68, please shoot them down or not:
  1. *Tile in the target by the strata of `Z` rather than by charts.* Near a point of `Z` where
     `Z` is locally the image of the divisor under several charts, the tangential-wall freedom
     (choose the neighbour's tangential coordinate whose level set is the given wall) needs the
     wall to be analytic and transverse in the neighbour's coordinates; the walls of a core are
     images `φ(T⁻¹({z_i = c} ∩ box))` of coordinate hypersurfaces, hence analytic hypersurfaces in
     the target **off the divisor image**, and near the divisor they are the images of hypersurfaces
     transverse to the divisor. Is there a clean sufficient condition on two monomial charts (e.g.
     "the transition `φ₂⁻¹∘φ₁` is analytic on the overlap of the open sets `W₁, W₂` *including the
     divisor*, and monomial in the divisor coordinates") under which a common refinement of two
     tilings exists? If such a condition is what real blow-up charts satisfy, the interface could be
     "monomial charts with analytic monomial transitions" and inhabitance from the readout would
     reduce to proving that hironaka's Q-induction produces such transitions.
  2. *Avoid gluing by monotone exhaustion of the low-phase set.* The sets `{K < ε}` are open;
     each hironaka chart covers a piece; the *measure* identity only needs a.e.-disjointness, so
     take `E₁ := image₁ ∩ Ω`, `E₂ := (image₂ ∖ E₁) ∩ Ω`, …; the problem is that `E₂` pulled back to
     chart 2 is not a product. But what if chart 2's *tangential base* is allowed to be an arbitrary
     measurable set **and the normal fibres of chart 2 over that base are either entirely inside
     `E₂` or entirely outside**? That is a saturation condition on `image₁` w.r.t. chart 2's fibres
     near the divisor — equivalent to the wall problem. So no free lunch; confirm.

**(D) Hironaka audit.** Concretely, what should the bounded audit look for in
`Monomialize/Analytic/BM89/*` (the `Q(n)` induction: `IsAdmissibleComposite` of moves
`blowUpChart`/`shear`/`translate`/`linear`, `IsQChart`, refinement of a `PartialResolution` by a
partial resolution of the pulled-back function)? Give me 3–5 yes/no questions to answer by reading
the code, and what answer pattern would make route (ii) viable.

**(E) Order of work.** Options: (1) restate the endpoint per (A) and prove the single-chart theorem
(B); (2) hironaka audit first; (3) paper bookkeeping for the bridge (dots for `exists_monomialTiling`
against `lem:adapted_pou`, `ExactNormalTiling.cutoffExpansion` against the main theorem, an honest
remark that the paper's adapted partition of unity is replaced by an exact measurable tiling and
that its "constant on normal fibres" construction is not what is formalised). Recommend an order
with stop rules.
