# Consult #91 — from the leading measure to the FULL expansion with strata-integral coefficients

You are Astra, advising the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, Mathlib v4.33.1, 597 modules, no sorry/axioms) of the grammar paper (Gerraty–Murfet). The user (Daniel Murfet) has just said, of the global leading-measure theorem (CCXC–CCXCVI, consults #89–#90): "this is far from the Taylor tree theorem identifying arbitrary coefficients in terms of strata integrals". He is right. Design the programme that closes that gap as far as the current interface allows, and say precisely where it cannot.

## The target in the paper
`thm:expectation_expansion`: `𝒵_n[φ] = Σ_I 𝒵_n[φ; I] + O(e^{−nε})`, `𝒵_n[φ; I] ~ Σ_k Σ_j C_{I,k,j}(φ) n^{−λ_{I,k}} (log n)^{j−1}`, with the coordinate-free expression
`𝒵_n[φ; I] ~ Σ_{r≥0} (1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩ τ_*|μ_I|` — the `r`-th conormal derivative of `φ∘π` (a section of `Sym^r N^*S_I`) contracted with the moment tensor `M_{I,r}(n) ∈ Γ(S_I, Sym^r N S_I)` (the `n`-dependence of the normal fibre moments, a finite power–log sum in `n`), integrated over the stratum against the pushed-forward density. Every coefficient `C_{I,k,j}(φ)` is thus a DISTRIBUTION on `W` supported on the zero set: a strata integral of normal derivatives of `φ∘π` of bounded order.

## What the library has
* Chart level, full expansion: `thm_TaylorTree_taylor` — on a one-sided box `(0,b]^{n+1}` with `K∘π = u^{2k}`, Jacobian `u^h`, amplitude `η` with a holomorphic extension to a polydisc of radius `R > b`, the population integral has a `TaylorTreeConclusion`: `C μ j = familySpectralCoeff … (Taylor families) μ j`, support in `Λ(h,k)`, absolutely convergent explicit series `Σ_p β^p/p! T_p(cη * J^{*p})`, quantitative remainder for every cutoff `L`. The coefficients are functionals of the Taylor coefficient family of `η` at the corner (canonical coefficient maps `dataBoxCoeff`, continuous on the weighted-ℓ¹ data space). Population version `population_TaylorTree_taylor`.
* Abstract expansions: `CutoffExpansion Q D Z c := ∀ L > 0, ∃ K, ∀ᶠ N, |Z N − Σ_{μ ∈ Q⁻¹ℕ, μ<L} N^{−μ} Σ_{j≤D} c μ j log^j N| ≤ K N^{−L}(1+log N)^D`; first-nonzero selection, flatness.
* Exact tiling / core decompositions (conditional): `cutoffExpansion_of_hasAnalyticCoreDecomposition` — a localisation datum with `μ = Σ_I core_I + tail` (each core carried exactly by a core presentation transporting the box measure `(ν ⊗ vol|_{(0,b]^{n+1}}) u^h c` onto the core measure, positive phase gap on the tail) has a full `CutoffExpansion` with coefficients `gCoeff = Σ_I tanCoeff …` (tangential integrals over the core base `K_I` of the chart Taylor-tree coefficients: `tanCoeff ν n h k β b x μ j = ∫_{K_I} (coefficient of the amplitude family at the base point) dν`). These `tanCoeff` ARE strata integrals in chart coordinates: an integral over the tangential base against `ν` of a functional of the normal Taylor coefficients of the amplitude at the base point. But the core presentation (exact normal form `K∘π = u^{2k}` on the whole core, measure transport) is a SUPPLIED certificate; hironaka's `IsMonomialChart` only gives `K∘φ = u(y)·y^e` with a continuous (in fact analytic) nonvanishing unit `u`, and the library removes the unit exactly by a rescaling of one divisor coordinate (`MonomialUnitRemoval.exact_normal_form`, local analytic normal form `K = β z^e`) — but only locally near a point, not on a whole chart.
* Resolved-space contraction identity (conditional, no exponents attached): `coverIntegral_eq_sum_pieceContraction` — under fibre power-series hypotheses for `F∘φ_i` on every chart–stratum piece, `𝒵_N[F] = Σ_{(i,I)} ∫_{piece_{i,I}} w_i (Σ_k ⟨D^k_⊥(F∘φ_i), M^κ_k⟩)(foot_I y) dy + exact divisor-free terms` (conditional contraction series over the coordinate stratum `P_I`); the conormal derivative machinery (`normalTaylorForm`, `IsGlobalNormalSection`, `conormalSplitting`, `SymmetricWeights`) is formalised fibrewise relative to a chosen normal family, no bundles constructed.
* Leading term, global (unconditional given a certified cover): the leading measure programme — `HasLeadingMeasure W K λ q σ` (scaled limits for all bounded continuous tests), canonical, concentrated on the zero set; `aeDisjointCoeff F = ∫ F dσ` with `σ = Σ_{tied (i,I,orthant)} (Φ_i ∘ facePoint)_* ν` and the explicit face density `β_w · ε^E · Γ(λ)/(m−1)! ∏ 1/(2k_j) · |v| |y_tang^h| (p∘φ) u^{−λ} ∏_{i∉J} u_i^{h_i−2k_iλ}` on base × unit box. Cube regression `σ = π^{d/2} δ₀`. Unconditional Θ-exponent over compact/bounded open `W`.
* Unconditional local: `IsMonomialChart.local_leading_term` (single chart at a divisor point, leading term with explicit positive coefficient; analytic units handled by freezing at the face); `exponent_of_analytic` (Θ over a compact neighbourhood of a zero from hironaka's `Q_all`).
* Hironaka interface: `PartialResolution` (finitely many compact chart domains, images covering a compact set a.e. with finite multiplicity — overlaps allowed, no common resolved space, no transition maps), `IsMonomialChart` (open `W ⊇ dom`, `φ` analytic on `W`, injective off the Jacobian monomial's zeros, `K∘φ = u y^e`, `det Dφ = v y^h` with `u, v` continuous nonvanishing on `W`).

## Questions
1. **The honest target.** What is the strongest theorem of the form "for a certified cover (a.e.-disjoint images, monomial charts), the original integral `∫_W φ ϕ e^{−nK}` has a full power–log cutoff expansion `Σ_{μ ∈ Λ, μ<L} Σ_j C_{μ,j}(φ) n^{−μ} log^j n + O(n^{−L})` whose EVERY coefficient `C_{μ,j}` is a distribution on `W` supported on the zero set, given explicitly by strata integrals of normal derivatives of `φ∘π` of order ≤ r(μ)" that can be proved from the present interface? Give the exact statement shape: what regularity of `φ` (analytic near the zero set? `C^∞`? the paper says analytic), how the distributions are represented in Lean (a finite family of measures on `W` paired with `φ`'s pulled-back normal derivatives? `∫_W ⟨D^r_⊥(φ∘π), M_r⟩ dσ_r` with `σ_r` measures and `M_r` measurable tensor fields? or the chart-sum form `Σ_{(i,I)} ∫_{base} (functional of the normal Taylor coefficients of φ∘φ_i at the face point) dν_{i,I}`?), and the precise sense of "canonical" (the coefficient DISTRIBUTIONS are canonical by uniqueness of the cutoff expansion — how far does that go given cancellations between charts?).
2. **The analytic unit.** The chart-level Taylor tree assumes the exact normal form `K∘π = u^{2k}` (unit = 1) on the box. hironaka gives `K∘φ = u(y) y^e` with an analytic nonvanishing unit on the whole chart neighbourhood. Which is the right route to the full expansion with a unit: (a) exact unit removal on each stratum piece by the rescaling `y_i ↦ y_i (u/β)^{1/e_i}` (already formalised locally) — does it extend to a whole compact stratum piece with a change of the tangential coordinates, and what does it do to the amplitude and the tangential base measure? (b) absorb the unit into the amplitude via the Taylor expansion of `u^{−λ}`-type factors in the normal variables (the unit is analytic, so `η(z, n) e^{−N u(z,n) n^{2k}}` = expansion in powers of `n` of `e^{−N(u−u(z,0))n^{2k}}` — the paper's dressed moments); (c) a "dressed" Taylor tree where the phase family has nonzero `ξ`-like corrections; (d) something else? The library already has a `TaylorTreeConclusion` with a PHASE coefficient family `cξ` (for `e^{−βN u^{2k} + β√N u^k ξ(u)}`) — can the analytic unit be fed through that phase slot?
3. **Assembly across strata and charts.** The core-decomposition expansion sums `tanCoeff` over cores; the leading-measure programme sums face measures over tied pieces. For the full expansion, what is the right global object for the coefficient of order `(μ, j)`: a measure `σ_{μ,j}` on `W` (only for `r = 0` terms) or a family of measures paired with derivatives? Is the correct statement "there exist finitely many finite measures `σ_{μ,j,r}` on `W` supported on the zero set and measurable symmetric tensor fields `T_{μ,j,r}` such that `C_{μ,j}(φ) = Σ_r ∫_W ⟨D^r_⊥(φ∘π), T_{μ,j,r}⟩ dσ_{μ,j,r}`"? How do the conormal derivatives `D^r_⊥(φ∘π)` live on `W` (they are objects on the resolved space at points of `S_I`; on `W` they are attached to points of the zero set `π(S_I)` — several strata can map to the same point)? Propose the honest Lean representation.
4. **Cancellations and canonicity.** Coefficients may vanish or cancel between charts; the cutoff expansion is unique (`first-nonzero`, uniqueness of coefficients given the lattice), so the coefficient functionals `φ ↦ C_{μ,j}(φ)` are canonical as functionals. Are they canonical as DISTRIBUTIONS (i.e. as pairings with derivatives), or only as functionals on the test class? What test class makes the representation unique?
5. **Plan.** Give an ordered unit plan (≤ 10 units, ≤ ~400 lines each) with exact statements, the library/Mathlib tools, sizes and gates, from the present state to the theorem in (1); name the first unit precisely and say which parts remain hypotheses at the end (certificates: disjointness, exact normal form or unit handling, analyticity of φ near the zero set) and what would need the upstream interface (common resolved space) to become intrinsic. If some part of the paper's statement (e.g. the coordinate-free `⟨D^r_⊥(φ∘π), M_{I,r}(n)⟩` with `M` as bundle sections) is not formalisable without a resolved space, say so and give the chart-level substitute.

## Key existing statements (verbatim)
```lean
structure TaylorTreeConclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (C : ℝ → ℕ → ℝ) : Prop where
  /-- `C` is the family spectral coefficient of the rescaled data. -/
  coeff_eq : ∀ μ j, C μ j = familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ j
  /-- Support: `C` vanishes off the paper's candidate exponent set `Λ(h,k)`. -/
  vanish : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0
  /-- The explicit series is absolutely convergent (`μ > 0`). -/
  summable : ∀ μ, 0 < μ → ∀ j,
    Summable fun p => |familyCoeffTerm n h k β (scale cξ b) (scale cη b) μ j p|
  /-- `C` equals the paper's Cauchy-product series `∑_p β^p/p! T_p(cη * J^{*p})`, every real `μ`. -/
  series : ∀ μ j, C μ j = familyCoeffSeries n h k β (scale cξ b) (scale cη b) μ j
  /-- Quantitative remainder for every cutoff, with `N b^{2|k|} ≥ 1`. -/
  remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N →
    |familyPhaseIntegralBox n h k β N b cξ cη - b ^ (∑ i, h i + (n + 1)) *
        ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) *
          ∑ j ∈ Finset.range (n + 1), C μ j * (Real.log (boxScale k b N)) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) *
        cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n)
  /-- Asymptotic form in the sample size. -/
  isBigO : ∀ L, 0 < L →
    (fun N : ℝ => familyPhaseIntegralBox n h k β N b cξ cη - boxSpectralSum n h k β L b cξ cη N)

def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop,
    |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)


/-- **The global weighted expansion over charts and strata**: under the paper's fibre power-series
hypotheses for the pulled-back observable `F ∘ φ_i` on every nonempty chart–stratum piece
(with the Boltzmann chart weight in the fibre measures), the resolved Boltzmann integral is the sum
over chart–stratum pairs `(i, I)` of the weighted conditional contraction series over the coordinate
stratum `P_I`, plus the exact contribution of the pieces away from the divisor. -/
theorem coverIntegral_eq_sum_pieceContraction (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε)
    {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hint : Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
      (volume.restrict (⋃ i, R.image i)))
    (q : ι → ∀ I : Finset (Fin d), I.Nonempty →
      (Fin (d - (I.card - 1 + 1)) → ℝ) → FormalMultilinearSeries ℝ (Fin (I.card - 1 + 1) → ℝ) ℝ)
    (Rad : ι → ∀ I : Finset (Fin d), I.Nonempty → (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ≥0∞)
    (hq : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, HasFPowerSeriesOnBall
      (fun n => F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) (q i I hne z) 0
      (Rad i I hne z))
    (hη : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, ∀ᵐ n ∂fibreMeasure volume
      (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
        (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z,
      n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad i I hne z))
    (hdom : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, Summable fun k =>
      ‖q i I hne z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
        (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z) :
    R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x) =
      ∑ i, ((∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
          ∫ y in sizePiece (D i) ε I,
            (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y *
              pieceContraction hε (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))
                (fun y => F ((R.chart i).φ y)) I y) +
        ∫ y in sizePiece (D i) ε ∅,
          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y)) := by
  rw [R.coverIntegral_eq_sum_chart_pieces N hN K hK hK0 p D ε hFm hint]
  refine Finset.sum_congr rfl fun i _ => ?_

  ∑ I, tanIntegral (ν I) (n I) (h I) (k I) β N (b I) (x.chart I)

/-- The global coefficients `∑_I 𝒞^I_{μ,j}(x_I)`. -/
noncomputable def gCoeff (x : JointData K n) (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ I, tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j

/-- The global ordered normalised remainder. -/
noncomputable def gRemainder (x : JointData K n) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  abstractRemainder (commonQ k) (commonD n) (gInt ν h k β b x) (gCoeff ν h k β b x) μ j N

theorem continuous_gCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ : ℝ)
    (j : ℕ) : Continuous fun x : JointData K n => gCoeff ν h k β b x μ j := by
  unfold gCoeff

111:theorem exact_normal_form {K u : (Fin d → ℝ) → ℝ} {e : Fin d →₀ ℕ} {β : ℝ} (hβ : 0 < β)
112-    {i : Fin d} (he : 0 < e i) {y : Fin d → ℝ} (hK : K y = u y * monomialEval y e)
113-    (hu : 0 < u y) : K y = β * monomialEval (rescale i (unitRoot β (e i) u) y) e := by
114-  rw [monomialEval_rescale, unitRoot_pow hβ he hu, hK]
115-  field_simp
116-
117-/-! ### Analyticity and the derivative of the rescaling -/
118-
119-/-- The rescaling is analytic where the scalar field is. -/
120-theorem analyticAt_rescale (i : Fin d) {r : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
121-    (hr : AnalyticAt ℝ r y) : AnalyticAt ℝ (rescale i r) y := by
--
212:theorem exists_localNormalForm {K u : (Fin d → ℝ) → ℝ} {e : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)}
213-    (hW : IsOpen W) (hu : AnalyticOnNhd ℝ u W) (hupos : ∀ y ∈ W, 0 < u y)
214-    (hK : ∀ y ∈ W, K y = u y * monomialEval y e) {β : ℝ} (hβ : 0 < β) {i : Fin d}
215-    (he : 0 < e i) {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (h0 : y₀ i = 0) :
216-    Nonempty (LocalNormalForm K β e W y₀) := by
217-  set r : (Fin d → ℝ) → ℝ := unitRoot β (e i) u with hr_def
218-  have hr : ∀ y ∈ W, AnalyticAt ℝ r y := fun y hy =>
219-    analyticAt_unitRoot hβ he (hu y hy) (hupos y hy)
220-  have hT : ∀ y ∈ W, AnalyticAt ℝ (rescale i r) y := fun y hy => analyticAt_rescale i (hr y hy)
221-  have hc : r y₀ ≠ 0 := (unitRoot_pos β (e i) u y₀).ne'
222-  -- the derivative at `y₀` is the invertible coordinate scaling

def HasLeadingMeasure (W : Set (Fin d → ℝ)) (K : (Fin d → ℝ) → ℝ) (lam : ℝ) (q : ℕ)
    (σ : Measure (Fin d → ℝ)) : Prop :=
  ∀ a : (Fin d → ℝ) →ᵇ ℝ, HasLeadingTerm (globalLaplace W K a) (∫ w, a w ∂σ) lam q


theorem hasLeadingTerm_targetIntegral_of_aeDisjoint (hdisj : R.AEDisjointImages)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) :
    HasLeadingTerm (targetIntegral (⋃ i, R.image i) F K p)
      (∫ x, F x ∂(R.leadingMeasure Ps hK0 hε hεb hpc hK hne hr0)) (R.partitionLam' Ps hne)
      (R.partitionDeg' Ps hne) := by
```
