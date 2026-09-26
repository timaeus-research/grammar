# Consult #168 — the empirical all-log formula: route choice after units 1–6 (Lean 4 / Mathlib, repo `timaeus-research/grammar`, namespace `Grammar`)

You are Astra, the design consultant for the polar-distribution formalisation programme (your consult #167 designed the 24-unit route). Units 1 (PolarAmplitudeAlgebra), 2 (ChartZetaStrip, with REAL amplitudes only), 3 (ChartZetaFace), 4 (ChartZetaRegularization), 5 (ChartZetaPolar) and 6 (ChartZetaPolarSupport) and 18 (LeadingFaceMeasure) have LANDED, axiom-clean. The verbatim Lean definitions and theorem statements are in the appendix below. Please read them first; in particular

* `chartZeta G h k s = ∫_{(0,1]^d} G(u) u^{h − 2ks} du` (real amplitude `G`), holomorphic on the flat strip `2kᵢ Re s < pᵢ + hᵢ + 1` when `|G| ≤ C u^p` (`hasDerivAt_chartZeta_flat`, dominated differentiation);
* `chartZetaAtDepth p F h k s = Σ_{(J,m) ∈ faceIndex p} faceW · innerFactor h k J m s · chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s`, equal to `chartZeta F h k s` on the strip, holomorphic on the flat strip off the finitely many candidate poles, and two depths agree (identity theorem on a strip minus a finite set, `isPreconnected_strip_diff_finite`);
* unit 5: `innerFactor = resConst · (μ − s)^{−poleOrder} · regularFactor` at a real `μ`, `faceHolo = regularFactor · chartZeta(faceAmp)` holomorphic near `μ`, the polar coefficients `chartPolarCoeff p F h k μ q` (coefficient of `(s−μ)^{−(q+1)}`) and ★★ `chartZetaAtDepth_sub_polarPart_isBigO_one : chartZetaAtDepth p F h k − polarPart D (chartPolarCoeff p F h k μ) μ = O(1)` on `𝓝[≠] μ` — exactly the input form of `polarCoeff_unique` (which identifies the polar data of `mellinContinuation Q D E c U` at `μ₀` with `polarCoeff c μ₀ q = (−1)^{q+1} q! c_{μ₀,q}` for ANY `a` with `mellinContinuation − polarPart D a μ₀ = O(1)`);
* unit 6: reality (`chartPolarReal`), support on the resonant stratum, jet congruence.

## The target

The library's empirical chart integral is
`empIntegral η ζ h k N = ∫_{(0,1]^d} η(v) v^h exp(−N v^{2k} + √N v^k ζ(v)) dv`
(`fieldFam η ζ τ v = η(v) e^{τ ζ(v)}`, `coupling k N v = √N v^k`), with the proven cutoff expansion `emp_cutoffExpansion : CutoffExpansion (Qamb k) (d−1) (empIntegral η ζ h k) (empCoeff η ζ h k)` (`empCoeff` is defined through the real face construction `empCoeffAtDepth` at the canonical depth). The programme's target is the ALL-LOG FORMULA identifying `empCoeff η ζ h k μ q` with polar functionals of the chart zeta functional applied to amplitudes built from `η`, `ζ` and the fluctuation function `S(s,a) = fluctuationCplx s a = ∫_0^∞ t^{s−1} e^{−t + a√t} dt`. In your #167 the plan was: units 7 `HolomorphicCubeFamily` (Taylor in `s` of a family of amplitudes with remainder controlled in a finite-jet seminorm), 8 `ChartZetaHolomorphicAmplitude`, 9 `ComplexFluctuation`, 10 `FluctuationAmplitudeFamily`, 11 `EmpiricalChartMellin` (`mellin (empIntegral) s = chartZeta(η · S(s,ζ)) h k s`), 12 `EmpiricalPolarCoefficients` = (*) via `polarCoeff_unique`.

## The decision I need

Because unit 2 was landed with REAL amplitudes (no complex-valued amplitude infrastructure), route A (the planned 7–12) now requires: complex-valued amplitude families `A : ℂ → ℝ^d → ℂ` holomorphic in `s`, holomorphy in `s` of the face amplitudes `faceAmp p J (A s) m w` (the coordinate-derivative/Taylor-remainder operators of the smooth engine commute with `∂_s̄` — an induction through `pd`, `pdPow`, `coordRem`, `remList` using second-derivative symmetry and the Cauchy–Riemann characterisation, on top of the existing joint-smoothness lemmas `pdMulti_slice_eq_iteratedFDeriv`, `contDiff_faceAmp_slice` for a parameter in a real normed space `B`, here `B = ℂ`), uniform flat bounds on discs, dominated differentiation of `s ↦ ∫ faceAmp(A s)(w) cpowWeight(s)(w) dw`, and the joint smoothness of `(s,a) ↦ S(s,a)` on `ℂ × ℝ` to all orders. I estimate 1500–2500 lines of genuinely new infrastructure.

**Route B (proposed): the coupling-integral representation.** Substituting `N = t/v^{2k}` in the Mellin transform and using Fubini twice,

  mellin (empIntegral η ζ h k) s = ∫_0^∞ t^{s−1} e^{−t} · chartZeta (fieldFam η ζ √t) h k s dt     (B1)

on the strip `0 < Re s`, `2kᵢ Re s < hᵢ + 1` (absolute convergence by AM–GM `√t ζ ≤ t/2 + ζ²/2`, `MellinTiltIntegrable.exp_tilt_le`). The amplitude `fieldFam η ζ √t` is REAL and `s`-independent for each `t`; the library already has its jets (`IsJet`), the uniform flat growth bound ★ `growthLE_faceAmp_fieldFam` (`|faceAmp p J (fieldFam η ζ τ) m w| ≤ C' · w^{p_K} (1+τ)^{|p|} e^{M'τ}`), joint continuity in `(τ,w)`, and the Mellin-moment interchange ★★ `mellinMom_pdMulti_fieldFam_zero` (`∫_0^∞ t^{μ−1} e^{−t} ∂^m[η e^{√t ζ}](v) dt = ∂^m[η · S_μ(ζ)](v)`). Then, with the unit-5 factorisation for the amplitude `fieldFam η ζ √t` at each `t`,

  ∫_0^∞ t^{s−1} e^{−t} chartZetaAtDepth p (fieldFam η ζ √t) h k s dt
    = Σ_{x=(J,m)} faceW · resConst_x · (μ−s)^{−c_x} · regularFactor_x(s) · Φ_x(s),          (B2)
  Φ_x(s) := ∫_0^∞ ∫_{box'} t^{s−1} e^{−t} faceAmp p J (fieldFam η ζ √t) m (w) · cpowWeight(s)(w) dw dt,

and `Φ_x` is holomorphic on the whole FLAT strip (which contains `μ`): the `s`-dependence is only through the explicit exponentials `t^{s−1}` and `cpowWeight(s)(w)` (derivative = integrand × (log t − 2 logSum k w)), dominated on compact sub-strips by the growth bound times `e^{−t}` — the same dominated-differentiation argument as unit 2 (`hasDerivAt_chartZeta_flat`) on the product measure. So the right-hand side `Z(s)` of (B2) is holomorphic on the flat strip minus the candidate poles, equals `mellin (empIntegral)` on the convergence strip by (B1), hence equals `mellinContinuation (Qamb k) (d−1) (empIntegral) (empCoeff) U` on the connected region `{0 < Re s < min(U, flatEdge)} \ (poles ∪ lattice)` (identity theorem, as in `chartZetaAtDepth_eq_of_depths`), in particular on a punctured neighbourhood of `μ`. Unit 5's polar theorem applied to the holomorphic factors `f_x := regularFactor_x · Φ_x` (it is really a general lemma about `Σ_x w_x (μ−s)^{−c_x} f_x(s)`) then gives `mellinContinuation − polarPart (d−1) a* μ = O(1)` with

  a*_q = Σ_{x : c_x ≥ q+1} faceW · resConst_x · (−1)^{c_x} · f_x^{(c_x−1−q)}(μ) / (c_x−1−q)!,      (B3)

and `polarCoeff_unique` gives `polarCoeff (empCoeff η ζ h k) μ q = a*_q` for `q ≤ d−1`, i.e. `empCoeff η ζ h k μ q = (−1)^{q+1}/q! · a*_q` — the empirical all-log formula in "integrated" form. Differentiating `Φ_x` under the integral (log powers) and Leibniz for `regularFactor_x · Φ_x`, then regrouping, (B3) becomes the coupling-average form

  a*_q = Σ_{r ≥ q+1} 1/(r−q−1)! ∫_0^∞ t^{μ−1} (log t)^{r−q−1} e^{−t} · chartPolarCoeff p (fieldFam η ζ √t) h k μ (r−1) dt,   (B4)

"the empirical polar coefficient is the Γ-weighted coupling average of the population polar functional `A_{μ,r}` of the tilted amplitude `η e^{√t ζ}`"; for `ζ = 0` the inner coefficient is `t`-independent and `∫ t^{μ−1}(log t)^j e^{−t} dt = Γ^{(j)}(μ)` gives the population all-log formula. Finally, pulling `A_{μ,r}` through the `t`-integral (linearity of the face construction plus `mellinMom_pdMulti_fieldFam_zero` extended through `remList`) would give your (*) with the amplitudes `η · ∂_s^{j} S(s,ζ)|_μ`; this interchange is a separate, optional statement (it needs the `a`-smoothness of `S(μ,·)`, which the library has: `contDiff_mul_fluctuation`).

Route B needs NO `s`-dependent amplitudes, no holomorphic-slice infrastructure, no joint smoothness of `S` in `(s,a)`. Its new analytic content is: (B1) (two Fubini interchanges + the known substitution `mellin_exp_tilt`), the absolute convergence and holomorphy of the double integrals `Φ_x` on the flat strip, the identity-theorem step, and (B4) (derivatives of parameter integrals with log weights, Leibniz). I estimate 800–1200 lines.

## Questions

1. **Correctness of route B.** Check (B1)–(B4) carefully: the Fubini conditions on the strip; the region for the identity theorem (note `mellinContinuation Q D E c U` is holomorphic on `{0 < Re s < U} \ latticeBelow Q U`, via `differentiableAt_mellin_cutoffRemainderFun`, and needs `hE : LocallyIntegrableOn (E : ℂ) (Ioi 0)`, `hE0 : E = O(1)` at `0⁺` — for `empIntegral` these follow from `MellinTiltIntegrable.locallyIntegrableOn_integral_tilt` / `integral_tilt_isBigO_one` with `ν = volume` on the box, bounded `ζ` and `η`); the degree bookkeeping (`polarCoeff_unique` gives `q ≤ D = d−1`; unit 5's `poleOrder ≤ d` so `q+1 ≤ d` covers everything — but is `polarPart (d−1)` versus `polarPart d` a problem when `d = 0`?); the sign/normalisation conventions (`polarCoeff c μ q = (−1)^{q+1} q! c_{μ,q}`; `chartPolarCoeff` uses `(μ−s)^{−c} = (−1)^c (s−μ)^{−c}` and Taylor in `(s−μ)`). Is (B4) exactly right, including the `(log t)` powers and factorials from `∂_s^ℓ t^{s−1} = t^{s−1} (log t)^ℓ`? Note `Φ_x` also carries `regularFactor_x(s)`, so `f_x^{(n)}(μ)` is a Leibniz sum; check that regrouping over faces really reproduces `chartPolarCoeff p (fieldFam η ζ √t) h k μ (r−1)` inside the `t`-integral (whose own definition is `Σ_{x : c_x ≥ r} faceW resConst (−1)^{c_x} (regularFactor_x · chartZeta(faceAmp(fieldFam √t)))^{(c_x−r)}(μ)/(c_x−r)!`).

2. **Is route B the right "deep" formulation, or a detour?** Your #167 perspective was that the primary object is the meromorphic distribution `T(s) = K^{−s} φ dw` and the empirical coefficients are its polar functionals applied to `G · ∂_s^{j} S(s,ζ)|_μ`. In route B the primary identity is (B1)/(B4): "`mellin(Z_N)(s) = ∫_0^∞ t^{s−1} e^{−t} ζ_{η e^{√t ζ}}(s) dt`, the Mellin transform of the empirical partition function is the Γ-weighted coupling average of the population zeta functional of the tilted amplitude", and (*) is the corollary obtained by pulling the polar functional through the coupling integral. For the paper: which statement should be the theorem and which the corollary? Is there a cleaner way to phrase (B4) as a statement about the distribution `T(s)` (e.g. as `Σ_r A_{μ,r}[ η · m_{r−q−1}(ζ) ]` with `m_j(a) = ∫ t^{μ−1}(log t)^j e^{−t+a√t} dt = ∂_s^j S(s,a)|_μ`, which is (*) again)? Please give the precise form you would print in the paper, with the sign conventions fixed to the library's.

3. **Unit decomposition for route B**, with Lean-level statements in the library's conventions (names, hypotheses, which existing lemmas to reuse — see the appendix), ordered by dependency, each unit ≤ ~400 lines. In particular: (i) the general "face-sum polar part" lemma abstracted from unit 5 (`Σ_x w_x (μ−s)^{−c_x} f_x − polarPart = O(1)` for an arbitrary finite family with `f_x` holomorphic near `μ`) — should it be added as a new file or should unit 5 be refactored (I prefer additive, keeping unit 5 as is)? (ii) the product-measure dominated differentiation for `Φ_x` — which Mathlib lemma (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `volume.prod`, or iterate: first the inner `w`-integral, then the outer `t`-integral, with the inner integral bounded by `C (1+√t)^{|p|} e^{M'√t}` times a strip constant)? (iii) how to get (B1): via `mellin_exp_tilt` and `integral_rpow_mul_exp_tilt_scaled`, or directly with the substitution `N = t/v^{2k}` per `v` (`mellin_comp_mul_left`) followed by unfolding `fluctuationCplx` and swapping? (iv) the identity-theorem region: reuse `isPreconnected_strip_diff_finite` with `P = poles ∪ latticeBelow` — is `{0 < Re s < min(U, flatEdge)}` the right region, and how should `U` be chosen relative to `μ` and the depth `p = depthOf h k L` (the flat edge is `min_i (pᵢ+hᵢ+1)/(2kᵢ) = L + 1/(2 max k)`)? (v) (B4): the cleanest Lean route to `iteratedDeriv n Φ_x μ = Σ_{i ≤ n} C(n,i) ∫∫ t^{μ−1}(log t)^{n−i} e^{−t} faceAmp · cpowWeight(μ) · (−2 logSum k w)^i` — or should `Φ_x` be organised as a Mellin transform in `t` of the function `t ↦ e^{−t} chartZeta(faceAmp(fieldFam √t))(s)` so that Mathlib's `mellin_hasDerivAt_of_isBigO_rpow` handles the `t`-derivatives while unit 2 handles the `w`-derivatives?

4. **The milestone (unit 14).** With (B4) in hand, what exactly should the `x²y²` regression against the library's `tendsto_logExample` compute, and is there a smaller sanity check (e.g. `d = 1`, `η = 1`, `ζ = 0`: `empCoeff = polar data of Γ(s)/(h+1−2ks)`) that should be done first?

5. Anything in route B that you consider a trap (measurability of `(t,w) ↦ faceAmp p J (fieldFam η ζ √t) m w` — the library has `measurable_uncurry_faceAmp_fieldFam` in `(w,τ)`; the `√t` reparametrisation; the `D` in `polarPart`; `μ` on the lattice vs off the lattice — `polarCoeff_unique` needs `μ₀ ∈ latticeBelow Q U`, but the chart candidate poles `(mᵢ+hᵢ+1)/(2kᵢ)` all lie on the lattice `(1/(2∏kᵢ))ℕ` — is that right?).

Answer with precise mathematics and Lean-level statements; be explicit where you disagree with route B. Use the library's names.

## Appendix: verbatim Lean statements (units 1–6 and the relevant library API)

### ChartZetaStrip.lean

/-- The complex monomial weight `∏ᵢ uᵢ^{hᵢ − 2kᵢ s}` written through the logarithmic sums. -/
noncomputable def cpowWeight (h k : ι → ℕ) (s : ℂ) (u : ι → ℝ) : ℂ :=
  Complex.exp ((logSum h u : ℂ) - 2 * s * (logSum k u : ℂ))

/-- The chart zeta functional `∫_{(0,1]^ι} G(u) ∏ᵢ uᵢ^{hᵢ − 2kᵢ s} du`. -/
noncomputable def chartZeta (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (s : ℂ) : ℂ :=
  ∫ u in SmoothEngine.box ι 1, (G u : ℂ) * cpowWeight h k s u

/-- The strip of absolute convergence for a `p`-flat amplitude: `2kᵢ Re s < pᵢ + hᵢ + 1`. -/
def FlatStrip (p h k : ι → ℕ) (s : ℂ) : Prop := ∀ i, 2 * (k i : ℝ) * s.re < p i + h i + 1

/-- The strip of absolute convergence for a bounded amplitude: `2kᵢ Re s < hᵢ + 1`. -/
def ZetaStrip (h k : ι → ℕ) (s : ℂ) : Prop := ∀ i, 2 * (k i : ℝ) * s.re < h i + 1

/-- A `p`-flat amplitude on the box: `|G w| ≤ C ∏ᵢ wᵢ^{pᵢ}`. -/
def FlatOn (G : (ι → ℝ) → ℝ) (p : ι → ℕ) (C : ℝ) : Prop :=
  ∀ w ∈ SmoothEngine.box ι 1, |G w| ≤ C * mono p w

/-- The integrand is integrable on the flat strip for a `p`-flat amplitude. -/
theorem integrableOn_chartZeta_integrand_flat {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ}
    (hflat : FlatOn G p C) (h k : ι → ℕ) {s : ℂ} (hs : FlatStrip p h k s) :
    IntegrableOn (fun u => (G u : ℂ) * cpowWeight h k s u) (SmoothEngine.box ι 1)

/-- ★ **Holomorphy on the flat strip**: the chart zeta functional of a `p`-flat amplitude is
complex-differentiable at every point of the flat strip, with derivative the log-weighted
integral. -/
theorem hasDerivAt_chartZeta_flat {G : (ι → ℝ) → ℝ} (hG : ContinuousOn G (SmoothEngine.box ι 1))
    {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C) (hflat : FlatOn G p C) (h k : ι → ℕ) {s : ℂ}
    (hs : FlatStrip p h k s) :
    HasDerivAt (chartZeta G h k)
      (∫ u in SmoothEngine.box ι 1,
        (G u : ℂ) * cpowWeight h k s u * (-2 * (logSum k u : ℂ))) s

theorem differentiableOn_chartZeta_flat {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hflat : FlatOn G p C) (h k : ι → ℕ) :
    DifferentiableOn ℂ (chartZeta G h k) {s | FlatStrip p h k s}

/-- At a real point the chart zeta functional is the real face integral of the smooth engine. -/
theorem chartZeta_ofReal (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (μ : ℝ) :
    chartZeta G h k (μ : ℂ) = (faceCoeffInt G h (fun i => 2 * k i) 1 μ 0 : ℂ)


### ChartZetaFace.lean

/-- ★ **The zeta face-term identity**: on the strip, the face-`J` term of the subset formula is
the sum over the face multi-indices of the inner rational factor times the complementary chart
zeta functional of the flat face amplitude. -/
theorem zeta_faceTerm_integral (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ}
    (hs : ZetaStrip h k s) :
    ∫ v in SmoothEngine.box (Fin d) 1,
        ((SmoothEngine.faceOp p J (List.finRange d) F v : ℝ) : ℂ) * cpowWeight h k s v =
      ∑ m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J),
        ((∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        (∏ i : {i // inJ J i},
          1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) *
        chartZeta (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i)
          (fun i => k i) s

/-- ★★ **The subset formula on the strip**: the chart zeta functional is the sum over the faces
of the inner rational factors times the complementary chart zeta functionals of the flat face
amplitudes. -/
theorem chartZeta_eq_sum_faces (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ}
    (hs : ZetaStrip h k s) :
    chartZeta F h k s =
      ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
        (∏ i : {i // inJ x.1 i},
          1 / (((x.2 i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) *
        chartZeta (SmoothEngine.faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
          (fun i => k i) s


### ChartZetaRegularization.lean

/-- ★ **A strip minus a finite set is preconnected.** -/
theorem isPreconnected_strip_diff_finite {c₁ c₂ : ℝ} (hc : c₁ < c₂) {P : Set ℂ}
    (hP : P.Finite) : IsPreconnected ({s : ℂ | c₁ < s.re ∧ s.re < c₂} \ P)

/-- The inner rational factor `∏_{i∈J} 1/(mᵢ + hᵢ + 1 − 2kᵢ s)`. -/
noncomputable def innerFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (s : ℂ) :
    ℂ :=
  ∏ i : {i // inJ J i}, 1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)

/-- The face sum at depth `p`, defined for every `s`. -/
noncomputable def chartZetaAtDepth (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (s : ℂ) : ℂ :=
  ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
    innerFactor h k x.1 x.2 s *
    chartZeta (SmoothEngine.faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
      (fun i => k i) s

/-- On the strip the face sum is the chart zeta functional (unit 3). -/
theorem chartZetaAtDepth_eq_chartZeta (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ} (hs : ZetaStrip h k s) :
    chartZetaAtDepth p F h k s = chartZeta F h k s

/-- `s` is a candidate pole at depth `p`: some inner denominator vanishes. -/
def PoleAt (p h k : Fin d → ℕ) (s : ℂ) : Prop :=
  ∃ x ∈ SmoothEngine.faceIndex p, ∃ i ∈ x.1,
    ((x.2 i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 = 0

/-- The candidate poles are the finitely many points `(mᵢ + hᵢ + 1)/(2kᵢ)`. -/
theorem finite_poleSet (p h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    {s : ℂ | PoleAt p h k s}.Finite

/-- The flat face amplitude is `p`-flat on the complementary box. -/
theorem flatOn_faceAmp (p : Fin d → ℕ) (J : Finset (Fin d)) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hp0 : ∀ i, 0 < p i) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Grammar.FlatOn (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => p i) C

/-- ★ **Holomorphy of the face sum** on the flat strip away from the candidate poles. -/
theorem differentiableOn_chartZetaAtDepth (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) :
    DifferentiableOn ℂ (chartZetaAtDepth p F h k)
      {s | FlatStrip p h k s ∧ ¬ PoleAt p h k s}

/-- The right edge of the flat strip: `min_i (pᵢ + hᵢ + 1)/(2kᵢ)`. -/
noncomputable def flatEdge (p h k : Fin d → ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => ((p i : ℝ) + h i + 1) / (2 * k i)

theorem flatStrip_iff_re_lt (p h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (s : ℂ) :
    FlatStrip p h k s ↔ s.re < flatEdge p h k

/-- ★★ **Depth compatibility**: two positive depths give the same continuation on the common
flat strip away from either set of candidate poles. -/
theorem chartZetaAtDepth_eq_of_depths {p p' : Fin d → ℕ} {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hp0 : ∀ i, 0 < p i)
    (hp0' : ∀ i, 0 < p' i) {s : ℂ} (hs : FlatStrip p h k s) (hs' : FlatStrip p' h k s)
    (hpole : ¬ PoleAt p h k s) (hpole' : ¬ PoleAt p' h k s) (hre : -1 < s.re) :
    chartZetaAtDepth p F h k s = chartZetaAtDepth p' F h k s


### ChartZetaPolar.lean

/-- Taylor remainder bound: a function holomorphic on a neighbourhood of `c` agrees with its
degree-`< n` Taylor polynomial at `c` up to `O(‖s − c‖^n)`. -/
theorem taylor_remainder_isBigO {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => f s - ∑ k ∈ range n, (k ! : ℂ)⁻¹ * iteratedDeriv k f c * (s - c) ^ k)
      =O[𝓝 c] fun s => ‖s - c‖ ^ n

/-- The principal part of `(c − s)^{−n} f(s)` at `c` for `f` holomorphic near `c`: the
coefficient of `(s − c)^{−(q+1)}` is `(−1)^n f^{(n−1−q)}(c)/(n−1−q)!`, and the difference is
bounded on a punctured neighbourhood of `c`. -/
theorem pole_taylor_isBigO_one {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    (fun s : ℂ => (c - s)⁻¹ ^ n * f s - ∑ q ∈ range n,
      (-1) ^ n * iteratedDeriv (n - 1 - q) f c / ((n - 1 - q)! : ℂ) / (s - c) ^ (q + 1))
      =O[𝓝[≠] c] fun _ => (1 : ℂ)

/-- The resonant coordinates of the face `(J, m)` at `μ`: `i ∈ J` with `mᵢ + hᵢ + 1 = 2kᵢ μ`. -/
noncomputable def faceResSet (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    Finset (Fin d) :=
  J.filter fun i => ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

theorem mem_faceResSet {h k : Fin d → ℕ} {J : Finset (Fin d)} {m : Fin d → ℕ} {μ : ℝ}
    {i : Fin d} :
    i ∈ faceResSet h k J m μ ↔ i ∈ J ∧ ((m i + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

theorem faceResSet_subset (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    faceResSet h k J m μ ⊆ J

/-- The pole order `c(J, m, μ)` of the face `(J, m)` at `μ`. -/
noncomputable def poleOrder (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    ℕ :=
  (faceResSet h k J m μ).card

theorem poleOrder_le_card (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ J.card

theorem poleOrder_le (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    poleOrder h k J m μ ≤ d

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
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 = 2 * ((k i : ℕ) : ℂ) * ((μ : ℂ) - s)

/-- ★ **Factorisation of the inner factor at `μ`**:
`innerFactor = (∏_res (2kᵢ)⁻¹) · (μ − s)^{−c} · regularFactor`, valid for every `s`. -/
theorem innerFactor_eq_res (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ)
    (s : ℂ) :
    innerFactor h k J m s =
      resConst h k J m μ * ((μ : ℂ) - s)⁻¹ ^ poleOrder h k J m μ * regularFactor h k J m μ s

/-- The regular factor is holomorphic wherever its denominators do not vanish. -/
theorem differentiableOn_regularFactor (h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ)
    (μ : ℝ) {U : Set ℂ}
    (hU : ∀ s ∈ U, ∀ i ∈ J \ faceResSet h k J m μ,
      ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0) :
    DifferentiableOn ℂ (regularFactor h k J m μ) U

/-- The set on which the face `(J, m)` is regular at depth `p`: the flat strip minus the
zeros of the non-resonant denominators. -/
def faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) : Set ℂ :=
  {s | FlatStrip p h k s ∧ ∀ i ∈ J \ faceResSet h k J m μ,
    ((m i + h i : ℕ) : ℂ) - 2 * ((k i : ℕ) : ℂ) * s + 1 ≠ 0}

theorem isOpen_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) :
    IsOpen (faceRegSet p h k J m μ)

/-- `μ` itself lies in the regular set once it lies in the flat strip. -/
theorem mem_faceRegSet (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : (μ : ℂ) ∈ faceRegSet p h k J m μ

theorem faceRegSet_mem_nhds (p h k : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : faceRegSet p h k J m μ ∈ 𝓝 (μ : ℂ)

/-- The holomorphic factor of the face `(J, m)` at `μ`: the regular factor times the
complementary chart zeta function of the face amplitude. -/
noncomputable def faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (μ : ℝ) (s : ℂ) : ℂ :=
  regularFactor h k J m μ s *
    chartZeta (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s

theorem differentiableOn_faceHolo (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) (μ : ℝ) :
    DifferentiableOn ℂ (faceHolo p F h k J m μ) (faceRegSet p h k J m μ)

/-- The face sum at depth `p`, with every inner factor factorised at `μ`. -/
theorem chartZetaAtDepth_eq_faceHolo (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (s : ℂ) :
    chartZetaAtDepth p F h k s = ∑ x ∈ SmoothEngine.faceIndex p,
      ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
        (((μ : ℂ) - s)⁻¹ ^ poleOrder h k x.1 x.2 μ * faceHolo p F h k x.1 x.2 μ s)

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
    chartPolarCoeff p F h k μ q = 0

/-- `μ` is a candidate pole at depth `p` iff some face has positive pole order. -/
theorem poleAt_iff_poleOrder (p h k : Fin d → ℕ) (μ : ℝ) :
    PoleAt p h k (μ : ℂ) ↔ ∃ x ∈ SmoothEngine.faceIndex p, 0 < poleOrder h k x.1 x.2 μ

theorem chartPolarCoeff_eq_zero_of_not_poleAt (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ)
    (h k : Fin d → ℕ) {μ : ℝ} (hμ : ¬ PoleAt p h k (μ : ℂ)) (q : ℕ) :
    chartPolarCoeff p F h k μ q = 0

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
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)

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
              ((poleOrder h k x.1 x.2 μ - 1 - q)! : ℂ) / (s - μ) ^ (q + 1)

/-- ★★ **The face sum minus its principal part is bounded near `μ`.**  For `F` smooth, at a
positive depth `p` whose flat strip contains `μ`, and for `D + 1` at least every pole order at
`μ`, `chartZetaAtDepth p F h k − polarPart D (chartPolarCoeff p F h k μ) μ = O(1)` on a
punctured neighbourhood of `μ`.  This is the input form of `polarCoeff_unique`. -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart D (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)

/-- The same with the universal degree bound `D = d` (every pole order is at most `d`). -/
theorem chartZetaAtDepth_sub_polarPart_isBigO_one' (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s - polarPart d (chartPolarCoeff p F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)

/-- Away from the candidate poles the face sum is itself bounded near `μ`. -/
theorem chartZetaAtDepth_isBigO_one_of_not_poleAt (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) (hpole : ¬ PoleAt p h k (μ : ℂ)) :
    (fun s : ℂ => chartZetaAtDepth p F h k s) =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)

/-- At the depth `depthOf h k L` with `L ≥ L₀ h`, every real `μ < L` lies in the flat strip. -/
theorem flatStrip_depthOf {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) : FlatStrip (depthOf h k L) h k (μ : ℂ)

/-- ★ The principal part of the face sum at the canonical depth `depthOf h k L`, for any real
`μ < L` (no candidate-pole hypothesis: the polar coefficients vanish when `μ` is not a pole). -/
theorem chartZetaAtDepth_depthOf_sub_polarPart_isBigO_one {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L)
    {μ : ℝ} (hμ : μ < L) :
    (fun s : ℂ => chartZetaAtDepth (depthOf h k L) F h k s -
      polarPart d (chartPolarCoeff (depthOf h k L) F h k μ) μ s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)


### ChartZetaPolarSupport.lean

/-- The polar coefficients as real numbers. -/
noncomputable def chartPolarReal (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  (chartPolarCoeff p F h k μ q).re

/-- ★ **Reality**: every chart polar coefficient at a real point is real. -/
theorem ofReal_chartPolarReal (p : Fin d → ℕ) (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ)
    (q : ℕ) : ((chartPolarReal p F h k μ q : ℝ) : ℂ) = chartPolarCoeff p F h k μ q

/-- The coordinates resonant at `μ` at depth `p`: `mᵢ + hᵢ + 1 = 2kᵢ μ` for some `mᵢ < pᵢ`. -/
noncomputable def resCoord (p h k : Fin d → ℕ) (μ : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i =>
    ∃ m ∈ Finset.range (p i), ((m + h i + 1 : ℕ) : ℝ) = 2 * (k i : ℝ) * μ

/-- The `r`-th resonant stratum of the closed unit box: at least `r` resonant coordinates
vanish. -/
def resStratum (p h k : Fin d → ℕ) (μ : ℝ) (r : ℕ) : Set (Fin d → ℝ) :=
  {v ∈ closedBox d 1 | r ≤ ((resCoord p h k μ).filter fun i => v i = 0).card}

/-- ★ **Support of the polar coefficients**: if all jets of `F` vanish on the `(q+1)`-st resonant
stratum then the `q`-th polar coefficient vanishes. -/
theorem chartPolarCoeff_eq_zero_of_jetsZeroOn (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ)
    (hF0 : JetsZeroOn F (resStratum p h k μ (q + 1))) :
    chartPolarCoeff p F h k μ q = 0

/-- ★ **Jet congruence**: amplitudes with equal rectangular `p`-jets on the `(q+1)`-st resonant
stratum have equal `q`-th polar coefficients. -/
theorem chartPolarCoeff_congr (p : Fin d → ℕ) {F G : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ)
    (hjet : EqJetsOn p F G (resStratum p h k μ (q + 1))) :
    chartPolarCoeff p F h k μ q = chartPolarCoeff p G h k μ q


### PolarAmplitudeAlgebra.lean

/-- The polar array `Σ_{j ∈ [q,D]} (−1)^{j+1} a j (j−q)/(j−q)!` of an amplitude family. -/
noncomputable def polarAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ j ∈ Ico q (D + 1), (-1 : ℂ) ^ (j + 1) * a j (j - q) / ((j - q).factorial : ℂ)

/-- The asymptotic coefficient `(1/q!) Σ_{j ∈ [q,D]} (−1)^{j−q} a j (j−q)/(j−q)!` (formula (*)). -/
noncomputable def logAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  (1 / (q.factorial : ℂ)) *
    ∑ j ∈ Ico q (D + 1), (-1 : ℂ) ^ (j - q) * a j (j - q) / ((j - q).factorial : ℂ)

/-- The real form of `logAmplitudeCoeff`, for real data `b`. -/
noncomputable def logAmplitudeCoeffReal (D : ℕ) (b : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  (1 / (q.factorial : ℝ)) *
    ∑ j ∈ Ico q (D + 1), (-1 : ℝ) ^ (j - q) * b j (j - q) / ((j - q).factorial : ℝ)

/-- Real data: the polar array is `polarCoeff` of the real coefficient system
`logAmplitudeCoeffReal`. -/
theorem polarAmplitudeCoeff_ofReal (D : ℕ) (b : ℕ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) :
    polarAmplitudeCoeff D (fun j ℓ => (b j ℓ : ℂ)) q =
      polarCoeff (fun _ q => logAmplitudeCoeffReal D b q) μ₀ q

/-- **The polar amplitude identity.** For `s ≠ μ` the polar sum minus the library's polar part
of the array `polarAmplitudeCoeff D a` is the polynomial remainder. -/
theorem polarAmplitudeSum_sub_polarPart (D : ℕ) (a : ℕ → ℕ → ℂ) (μ : ℂ) {s : ℂ}
    (hs : s ≠ μ) :
    polarAmplitudeSum D a μ s - polarPart D (polarAmplitudeCoeff D a) μ s =
      polarAmplitudeRemainder D a μ s


### PrincipalPartUniqueness.lean

/-- The polar part `Σ_{q≤D} a_q/(s−μ)^{q+1}`. -/
noncomputable def polarPart (D : ℕ) (a : ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (D + 1), a q / (s - μ) ^ (q + 1)

/-- The continuation expression `F_U = mellin R_U + principalParts U` (`MellinRegularization`). -/
noncomputable def mellinContinuation (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) :
    ℂ :=
  mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s

/-- The polar coefficients at `μ₀` in the standard `(s−μ₀)^{−(q+1)}` convention:
`a_q = (−1)^{q+1} q! c_{μ₀,q}`. -/
noncomputable def polarCoeff (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) : ℂ :=
  (-1) ^ (q + 1) * (q.factorial : ℂ) * (c μ₀ q : ℂ)

/-- ★★★ **Uniqueness of the polar coefficients of a cutoff expansion**: any polar part `a` at a
retained exponent `0 < μ₀ < U` with `F_U − polarPart D a μ₀ = O(1)` near `μ₀` has
`a_q = (−1)^{q+1} q! c_{μ₀,q}` — the coefficients of `N^{−μ₀}(log N)^q` are the unique local
principal-part data of the continued Mellin transform. -/
theorem polarCoeff_unique (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) {a : ℕ → ℂ}
    (ha : (fun s => mellinContinuation Q D E c U s - polarPart D a (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = polarCoeff c μ₀ q


### MellinRegularization.lean

/-- The principal parts `Σ_{μ<U} Σ_{q≤D} c_{μ,q} · q!/(μ − s)^{q+1}`. -/
noncomputable def principalParts (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
    (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))

/-- The regularised function `E − 𝟙_{[1,∞)} P_U`, complexified. -/
noncomputable def cutoffRemainderFun (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (N : ℝ) :
    ℂ :=
  (E N : ℂ) - ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N

/-- ★★ **Complex differentiability of the regularised Mellin transform on the strip
`0 < Re s < U`.** -/
theorem differentiableAt_mellin_cutoffRemainderFun (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hsU : s.re < U) :
    DifferentiableAt ℂ (mellin (cutoffRemainderFun Q D E c U)) s

/-- ★★ **The Mellin transform of `E` with its principal parts on the initial strip**: for
`0 < Re s < a`, where `E = O(N^{−a})` at infinity and every retained exponent with a nonzero
coefficient is `≥ a`,
`mellin E s = mellin R_U s + Σ_{μ<U} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`. -/
theorem mellin_eq_mellin_cutoffRemainderFun_add_principalParts (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U a : ℝ} (haU : a ≤ U)
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → a ≤ μ) {s : ℂ}
    (hs0 : 0 < s.re) (hsa : s.re < a) :
    mellin (fun N => (E N : ℂ)) s =
      mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s


### AbstractExpansion.lean

/-- The spectral sum of an abstract coefficient system below the cutoff `L`. -/
noncomputable def absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j

/-- **Finite-cutoff expansion** of `Z` on the lattice `Q⁻¹ℕ` with log degrees `≤ D` and
coefficients `c`. -/
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop,
    |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)


### EmpiricalGeneral.lean

/-- The empirical integral `∫_{(0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`. -/
noncomputable def empIntegral (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
    exp (-N * mono (fun i => 2 * k i) v)

/-- ★★★ **The canonical empirical coefficients**: the depth-`2kL−h` coefficients at the
deterministic cutoff `L = max(⌊μ⌋₊ + 1, L₀)`. -/
noncomputable def empCoeff (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ) : ℝ :=
  empCoeffAtDepth η ζ h k (depthOf h k (cutoffOf h μ)) μ q

/-- ★★★ **The empirical integral is a cutoff expansion** on the lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, with
logarithmic degree `≤ d − 1` and the canonical coefficients `empCoeff`: for every `L > 0` there is
`K` with
`|∫_{(0,1]^d} η v^h e^{−N v^{2k} + √N v^k ζ} dv`
`  − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} empCoeff μ q (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` eventually in `N`. -/
theorem emp_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k)

/-- ★★ **Canonicity**: any cutoff expansion of the empirical integral on the lattice `Q⁻¹ℕ` with
logarithmic degree `≤ d − 1` has the coefficients `empCoeff`. -/
theorem empCoeff_unique (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = empCoeff η ζ h k μ j


### EmpiricalGeneralDepth.lean

/-- The empirical face coefficients of a field factor `G` (zero for the empty face). -/
noncomputable def empFaceCoef (e : Fin d → ℕ) (G : ℝ → ℝ) : ℝ → ℕ → ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceInnerCoeff (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) G
  else fun _ _ => 0

/-- The pointwise coupling `τ = √N v^k`. -/
noncomputable def coupling (k : Fin d → ℕ) (N : ℝ) (v : Fin d → ℝ) : ℝ := Real.sqrt N * mono k v

/-- ★ **The empirical coefficient system at depth `p`** on the ambient lattice: for each face
`(J, m)`, the binomially reindexed face coefficient integrals of the empirical face coefficients of
the face amplitude family. -/
noncomputable def empCoeffAtDepth (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (μ : ℝ) (q : ℕ) :
    ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q) *
    faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)


### SmoothGeneral.lean

/-- The depth for the cutoff `L`: `pᵢ = 2kᵢL − hᵢ`. -/
def depthOf (h k : Fin d → ℕ) (L : ℕ) : Fin d → ℕ := fun i => 2 * k i * L - h i

/-- The first cutoff at which every depth is positive. -/
def L₀ (h : Fin d → ℕ) : ℕ := (∑ i, h i) + 1

theorem depthOf_add {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) (i : Fin d) :
    depthOf h k L i + h i = 2 * k i * L

theorem depthOf_pos {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) (i : Fin d) :
    0 < depthOf h k L i

/-- The cutoff used to define the coefficient at the exponent `μ`. -/
noncomputable def cutoffOf (h : Fin d → ℕ) (μ : ℝ) : ℕ := max (⌊μ⌋₊ + 1) (L₀ h)


### EmpiricalFieldFamilyJets.lean

/-- The empirical field family `B_τ(v) = η(v) e^{τ ζ(v)}`. -/
noncomputable def fieldFam (η ζ : (Fin d → ℝ) → ℝ) (τ : ℝ) (v : Fin d → ℝ) : ℝ :=
  η v * exp (τ * ζ v)

theorem contDiff_fieldFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => fieldFam η ζ z.1 z.2

/-- `H τ v = (∑_{r ≤ R} P_r(v) τ^r) e^{τ ζ(v)}` with smooth coefficient functions `P_r`. -/
def IsJet (ζ : (Fin d → ℝ) → ℝ) (R : ℕ) (H : ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ P : ℕ → (Fin d → ℝ) → ℝ, (∀ r, ContDiff ℝ ∞ (P r)) ∧
    ∀ τ v, H τ v = (∑ r ∈ range (R + 1), P r v * τ ^ r) * exp (τ * ζ v)

/-- ★ **Uniform jet bound**: the coordinate derivatives `∂^m B_τ`, `m ≤ p`, are bounded on the
closed box by `C (1+τ)^{|p|} e^{M'τ}` with ONE constant `C`. -/
theorem exists_pdMulti_fieldFam_bound (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b M' : ℝ}
    (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ →
      ∀ v ∈ closedBox d b, |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤
        C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ)

/-- ★ **Flat growth of the empirical face amplitudes** (existential form). -/
theorem growthLE_faceAmp_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b M' : ℝ}
    (hb : 0 < b) (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Finset (Fin d)) (m : Fin d → ℕ), m ∈ idxL p (lJ J) →
      ∀ w ∈ box {i // ¬ inJ J i} b,
        GrowthLE (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
          ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
            mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M'

/-- The face amplitudes of the field family are jointly continuous in `(τ, w)`. -/
theorem continuous_faceAmp_fieldFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Continuous fun z : ℝ × ({i // ¬ inJ J i} → ℝ) => faceAmp p J (fieldFam η ζ z.1) m z.2


### EmpiricalInnerKernel.lean

/-- `|G(τ)| ≤ A (1+τ)^m e^{Mτ}` for `τ ≥ 0`. -/
def GrowthLE (G : ℝ → ℝ) (A : ℝ) (m : ℕ) (M : ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → |G τ| ≤ A * (1 + τ) ^ m * exp (M * τ)

/-- The moment kernel `s^{μ−1} (−log s)^ℓ · G(√s) e^{−s}`. -/
noncomputable def momKernel (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) (s : ℝ) : ℝ :=
  s ^ (μ - 1) * (-log s) ^ ℓ * (G (Real.sqrt s) * exp (-s))

/-- The log-weighted Mellin moment `∫₀^∞ s^{μ−1} (−log s)^ℓ G(√s) e^{−s} ds`. -/
noncomputable def mellinMom (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), momKernel G μ ℓ s


### EmpiricalMellinJet.lean

/-- The Mellin field `v ↦ ∫₀^∞ s^{μ−1} e^{−s} H(√s, v) ds` of a coupling family. -/
noncomputable def mellinField (H : ℝ → (Fin d → ℝ) → ℝ) (μ : ℝ) (v : Fin d → ℝ) : ℝ :=
  mellinMom (fun τ => H τ v) μ 0

/-- The Mellin field of the field family is `η · S_μ(ζ)`. -/
theorem mellinField_fieldFam (μ : ℝ) :
    mellinField (fieldFam η ζ) μ = fun v => η v * fluctuation 1 μ (ζ v)

/-- ★★ **The Mellin moments of the field jets are the jets of `η · S_μ(ζ)`**:
`∫₀^∞ s^{μ−1} e^{−s} ∂^m_v[η e^{√s ζ}](v) ds = ∂^m_v[η(v) S_μ(ζ(v))]`. -/
theorem mellinMom_pdMulti_fieldFam_zero (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ}
    (hμ : 0 < μ) (m : Fin d → ℕ) (l : List (Fin d)) (v : Fin d → ℝ) :
    mellinMom (fun τ => pdMulti m l (fieldFam η ζ τ) v) μ 0 =
      pdMulti m l (fun v => η v * fluctuation 1 μ (ζ v)) v

/-- The jets of `η · S_μ(ζ)` are smooth (they are Mellin fields of jets). -/
theorem contDiff_mul_fluctuation (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ} (hμ : 0 < μ) :
    ContDiff ℝ ∞ fun v => η v * fluctuation 1 μ (ζ v)


### Fluctuation.lean

/-- The **fluctuation function** `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`
(grammar §4 `eq:fluctuation`; Watanabe, Definition 5.8). -/
noncomputable def fluctuation (β lam a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)


### FluctuationComplex.lean

/-- The fluctuation function at a complex index. -/
noncomputable def fluctuationCplx (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Real.exp (-t + a * Real.sqrt t) : ℂ)

/-- At a real index the complex fluctuation function is the real one. -/
theorem fluctuationCplx_ofReal (lam a : ℝ) :
    fluctuationCplx (lam : ℂ) a = (fluctuation 1 lam a : ℂ)

/-- ★ **The Mellin transform of the tilted phase**: for `K > 0`,
`∫_0^∞ N^{s−1} e^{−NK + √N H} dN = K^{−s} S_s(H/√K)`. -/
theorem mellin_exp_tilt {K : ℝ} (hK : 0 < K) (H : ℝ) (s : ℂ) :
    mellin (fun N : ℝ => (Real.exp (-N * K + Real.sqrt N * H) : ℂ)) s =
      (K : ℂ) ^ (-s) * fluctuationCplx s (H / Real.sqrt K)


### MellinTiltIntegrable.lean

/-- AM–GM for the tilt: `e^{−NK+√N H} ≤ e^{H²/(2K)} e^{−NK/2}`. -/
theorem exp_tilt_le {K : ℝ} (hK : 0 < K) (H : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    Real.exp (-N * K + Real.sqrt N * H) ≤
      Real.exp (H ^ 2 / (2 * K)) * Real.exp (-(K / 2) * N)

/-- The Mellin integrand of the tilted exponential is integrable on `(0,∞)` for `σ > 0`. -/
theorem integrableOn_rpow_mul_exp_tilt {K : ℝ} (hK : 0 < K) (H : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun N : ℝ => N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * H)) (Ioi 0)

/-- ★ **The scaled Mellin integral**: `∫_0^∞ N^{σ−1} e^{−NK + √N a√K} dN = K^{−σ} S_σ(a)`. -/
theorem integral_rpow_mul_exp_tilt_scaled {K : ℝ} (hK : 0 < K) (a σ : ℝ) :
    ∫ N in Ioi (0 : ℝ), N ^ (σ - 1) * Real.exp (-N * K + Real.sqrt N * (a * Real.sqrt K)) =
      K ^ (-σ) * fluctuation 1 σ a


### SmoothFaceSplit.lean

/-- The flat face amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)`. -/
noncomputable def faceAmp (m : Fin d → ℕ) (w : {i // ¬ inJ J i} → ℝ) : ℝ :=
  remList p (lK J) (pdMulti m (lJ J) F) (glue J 0 w)

/-- ★ **Flatness of the face amplitude**: under the rectangular mixed-derivative bound
`|∂^m F| ≤ M` for `m ≤ p`, `|G_{J,m}(w)| ≤ (∏_{i∈K} 1/(p_i−1)!) · M · w^{p_K}` on the box. -/
theorem faceAmp_bound (hF : ContDiff ℝ ∞ F) {b : ℝ} (hb : 0 < b) (hp0 : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M)
    {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) :
    |faceAmp p J F m w| ≤
      (∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * M *
        mono (fun i : {i // ¬ inJ J i} => p i) w


### SmoothFaceTheorem.lean

/-- The face coefficient integral `∫_{(0,b]^ι} G(w) w^h (w^a)^{−μ} S(w)^e dw`. -/
noncomputable def faceCoeffInt (G : (ι → ℝ) → ℝ) (h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : ℝ :=
  ∫ w in box ι b, G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e


### ParametricFaceAmplitude.lean

/-- ★ The face amplitude of a jointly smooth slice family is jointly smooth in the parameter and
the complementary coordinates. -/
theorem contDiff_faceAmp_slice (hG : ContDiff ℝ ∞ G) (p : Fin d → ℕ) (J : Finset (Fin d))
    (m : Fin d → ℕ) :
    ContDiff ℝ ∞ fun z : B × ({i // ¬ inJ J i} → ℝ) =>
      faceAmp p J (fun v => G (z.1, v)) m z.2

