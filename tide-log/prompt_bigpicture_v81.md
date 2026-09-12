# Consult #81 — grammar Lean: #80 units 1–3 landed (+ posterior check); planning R2 (normal-dependent unit)

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
553 modules, axiom-clean). Your #80 programme: R1 residual formula → x²y⁴ example → fidelity
consolidation → R2 normal-dependent unit → R3 supplied weights / R4 dependency statement.

## Landed since #80 (exact statements in the appendix)
* CCL `ResidualFaceCoefficient`: projected-orthant residual formula, scaling identity, `faceLeadConst_one_eq`
  (product over the MINIMAL coordinates), reflection reduction `∑_σ = 2^{|J|} ∑_{residual signs}`
  (`sum_reduce_of_indep` via `Equiv.piEquivPiSubtypeProd`), `ScalarUnitCell.reflected_coeff_eq`,
  `pieceAtlas_sum_tied_residual`.
* CCLI `MixedExponentExample`: `K = y₀²y₁⁴` on `[−1,1]²`: `(λ*,k*) = (1/4, 0)`, minimal set `{1}`, tied strata
  `{1}` (null base at cutoff `ε = b = 1`) and `{0,1}` (residual exponent `−1/2`); `∫_{(0,1]²} u₀^{−1/2} = 2`,
  face constant `Γ(1/4)/4`, tied sum `2·2·Γ(1/4)/4·2 = 2Γ(1/4)`; ★ `∫_{[−1,1]²} e^{−N x²y⁴} ~ 2Γ(1/4) N^{−1/4}`
  (positivity from the computed value — your predicted constant came out exactly).
* CCLII `MixedExponentPosterior`: the piece computation generalised over the observable (`tiedSum_univ_of_inner`,
  `productCoeffD_eq_of_inner = Γ(1/4)·R`); for `F = y₀²`: `R = ∫₀¹ t² t^{−1/2} = 2/5`, so
  ★ `E_N[y₀²] → (Γ(1/4)·2/5)/(2Γ(1/4)) = 1/5` — your predicted 1/5.
* Fidelity consolidation: the mirror now carries a scope remark (deterministic Gibbs leading-limit theorem
  for a cover of centred product charts with normal-independent units and factoring cover weights; totalised
  quotient `E_N`; not the empirical posterior; not the full expansion; hypotheses not yet derived from a
  resolution).

## The library already has a normal-dependent-unit theorem — LOCALLY (Astra #70 route C, CCV)
`IsMonomialChart.local_leading_term` (appendix): for a general monomial chart (unit `u` analytic on `W`, NOT
normal-independent), analytic `K ≥ 0` and analytic `F` with `F(φ y₀) > 0`, some compact region `Ω ∋ φ y₀`
has `∫_Ω F e^{−NK} ~ c N^{−λ} log^{m−1} N`, `c > 0`. Its mechanism: a **strip normalisation** — the
`2k_{j₀}`-th root of the unit is absorbed into ONE normal coordinate by an analytic change of variables
(`unitRoot`, `StripData`, `stripChart`; `exists_stripData`), the region becomes the image of a box under the
strip chart (`localRegion = stripChart '' zBox`), and the population coefficient theory + the analytic core
decomposition (all-orders cutoff expansion with analytic amplitude) identify the leading term. Cost: the
amplitude must be ANALYTIC; the region is a chart image (not a product box); no assembly across strata/charts;
coefficient is the assembled canonical coefficient (positive), not a face integral in the original data.

The product-chart assembly (CCXLI–CCLII) instead works with CONTINUOUS data (scalar-unit cells:
`K∘Φ(Ψ(z,n)) = q(z) ∏ n_a^{2k_a}` with the unit `q` independent of `n` on the piece, continuous amplitude `A`),
gives explicit face-integral coefficients and the posterior limit, but requires `unit_indep : u y = u (P_J y)`.

## Candidates for R2 (removing `unit_indep`)
(A) **Strip normalisation inside a piece**: on each stratum piece apply CCV's `stripChart` to absorb the unit's
    variation into one normal coordinate; the image is no longer a product box (variable strip), so the piece
    decomposition/fibre saturation would have to be redone in the strip coordinates. Heavy; analytic amplitude.
(B) **Localisation-comparison (squeeze at the leading order)**: for a positive continuous unit `u(z,n)` on the
    compact piece, for every `δ > 0` pick `η` with `|u(z,n) − u(z,0)| ≤ δ u(z,0)` for `|n| ≤ η` (uniform
    continuity), split the normal box into `{|n| ≤ η}` and the rest; on the small box the kernel is sandwiched
    between the constant-unit kernels with units `(1±δ) u(z,0)` (monotonicity of `e^{−N u ∏n^{2k}}` in `u`,
    positive amplitude), whose certificates are known (CCXXXI) with coefficients `((1±δ) u(z,0))^{−λ}·faceCoeff`;
    the complement `{∃ a, |n_a| ≥ η}` is dominated by cells with fewer minimal coordinates ⇒ lower log degree
    (this is exactly the existing size-piece/stratum machinery applied INSIDE the normal box) — so
    `limsup/liminf` of `Z_N / (N^{−λ} log^{k} N)` are within a factor `(1±δ)^{−λ}` of the target coefficient
    `∫ β u(z,0)^{−λ} A(z,0)·C`, and `δ → 0` gives the leading term with coefficient
    `∫_base β(z) u(z,0)^{−λ} A(z,0) dz · C` — the unit evaluated at the normal ORIGIN.
    You warned (#80): the correct residual-case coefficient freezes the unit on the MINIMAL FACE
    `u(z, (0_M, v_L))`, not at the origin. In the ALL-MINIMAL case (`J = all normal coordinates`) the face is the
    origin and (B) is right; for residual strata the sandwich must keep the `L`-coordinates: sandwich only in
    the `M`-directions? (i.e. `|u(z,(n_M,n_L)) − u(z,(0,n_L))| ≤ δ` uniformly for `|n_M| ≤ η`.)
    Requirements for (B): sign condition on the amplitude (positive or handle signed amplitude by splitting
    `A = A⁺ − A⁻`), the `HasLeadingTerm` certificate for the constant-unit kernel with the SAME base weight
    (CCXXXI/CCXXXII), and a "negligible complement" lemma. Output: a `HasLeadingTerm` for the variable-unit cell.
(C) **Reduce to (A) via a product-preserving normalisation**: if the unit depends on `n` only through a single
    coordinate … not general.
(D) Skip R2; do R3 (supplied regular weights entering the amplitude) first — it may be needed for R4 anyway
    and is more "interface" than analysis.
(E) Other paper-facing items: subleading terms; the empirical transfer; a `k* ≥ 1` non-all-minimal example
    (`K = x²y²z⁴`?) to test the log factor with residual coordinates; consolidating a top-level statement
    for the paper (thm:expectation_expansion leading-order version) as ONE theorem with the paper's notation.

Q1. Rank (A)–(E) for the next 3–5 units, with reasons. Is (B) mathematically sound as sketched (in particular
    the "negligible complement" claim and the residual-face version with `M`-only sandwiching)? What is the
    cleanest Lean statement for a variable-unit scalar cell certificate (`HasLeadingTerm` of
    `∫_base β ∫_{[−b,b]^{n+1}} A(z,n) ∏|n_a|^{h_a} e^{−N u(z,n) ∏ n_a^{2k_a}} dn dz`)?
Q2. For the top item, module contracts (statements, reuse of the appendix declarations, pitfalls).
Q3. Any misstatement in CCL–CCLII (appendix)? In particular the residual formula's `b^{Σ_{a∉J}(α_a+1)}` and the
    face constant with `∏_{a∈J} 1/(2k_a)`; the x²y⁴ coefficient `2Γ(1/4)` with the `{1}`-piece null at
    `ε = b` (is the cutoff-independence theorem enough to claim the same value for `ε < 1`? — yes by
    `productCoeffD_eq_of_cutoff`, but note the {1}-piece then has positive mass and the {0,1}-piece has
    `b^{1/2}` — they must sum to the same `2Γ(1/4)`; a consistency check we could formalise).

## Appendix — exact Lean statements

```lean
-- Grammar/StripBoxExpansion.lean
structure StripData (i : Fin d) (V : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (Q₀ : Set (Fin d → ℝ)) where
  /-- the strip height -/
  b₀ : ℝ
  /-- the output cylinder height -/
  b : ℝ
  b₀_pos : 0 < b₀
  b_pos : 0 < b
  /-- the open strip -/
  S : Set (Fin d → ℝ)
  S_open : IsOpen S
  S_sub : S ⊆ V
  cyl_sub : cylinder i Q₀ (b₀ / 2) ⊆ S
  injOn : InjOn (rescale i ρ) S
  jac_pos : ∀ y ∈ S, 0 < ρ y + y i * fderiv ℝ ρ y (Pi.single i 1)
  image_open : IsOpen (rescale i ρ '' S)
  cyl_sub_image : cylinder i Q₀ b ⊆ rescale i ρ '' S
  inv_analytic : ∀ z ∈ rescale i ρ '' S, AnalyticAt ℝ (Function.invFunOn (rescale i ρ) S) z

```

```lean
-- Grammar/ChartOrthantTiling.lean
noncomputable def stripChart (ζ : Fin d → ℝ) : Fin d → ℝ := translated φ y₀ (SD.inv ζ)

theorem orthantChart_eq (s : Fin (C.n + 1) → Bool) :
    orthantChart C SD s = stripChart C SD ∘ splitReflect C.σ s := rfl
```

```lean
-- Grammar/ChartOrthantTiling.lean
def localRegion (A' : Set (Fin C.t → ℝ)) (b' : ℝ) : Set (Fin d → ℝ) :=
```

```lean
-- Grammar/ChartLeadingTerm.lean
theorem chart_local_leading_term (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    (hKm : Measurable K) (hK0 : ∀ w ∈ C.V₀, 0 ≤ K (translated φ y₀ w)) {F : (Fin d → ℝ) → ℝ}
    (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (hA : IsCompact A)
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hAvol : ∀ r : ℝ, 0 < r → 0 < volume (A ∩ Metric.closedBall 0 r))
    (hb₁ : 0 < b₁) {U' : Set (Fin d → ℝ)} (hU' : IsOpen U') (hy₀U' : φ y₀ ∈ U')
    (hFU' : ∀ x ∈ U', 0 < F x) :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧ b' ≤ b₁ ∧ b' ≤ SD.b ∧
      IsCompact (localRegion C SD (A ∩ Metric.closedBall 0 B) b') ∧
      φ y₀ ∈ localRegion C SD (A ∩ Metric.closedBall 0 B) b' ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ translated φ y₀ '' C.V₀ ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ U' ∧
      0 < localLeadingCoeff C SD F (A ∩ Metric.closedBall 0 B) b' ∧
        (fun N => ∫ x in localRegion C SD (A ∩ Metric.closedBall 0 B) b',
          F x * Real.exp (-N * K x)) ~[atTop]
        fun N => localLeadingCoeff C SD F (A ∩ Metric.closedBall 0 B) b' *
          (N ^ (-C.lam) * Real.log N ^ (C.mult - 1)) := by
```

```lean
-- Grammar/ChartLeadingTerm.lean
theorem IsMonomialChart.local_leading_term {dom : Set (Fin d → ℝ)} {e : Fin d →₀ ℕ}
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0)
    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) (hFpos : 0 < F (φ y₀)) :
    ∃ C : CentredChartData K φ h y₀, ∃ Ω : Set (Fin d → ℝ), IsCompact Ω ∧ φ y₀ ∈ Ω ∧
      Ω ⊆ φ '' W ∧ Ω ⊆ U ∧ (∃ V : Set (Fin d → ℝ), IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, φ y ∈ Ω) ∧
      ∃ c : ℝ, 0 < c ∧
        (fun N => ∫ x in Ω, F x * Real.exp (-N * K x)) ~[atTop]
          fun N => c * (N ^ (-C.lam) * Real.log N ^ (C.mult - 1)) := by
```

```lean
-- Grammar/CentredChart.lean
structure CentredChartData (K : (Fin d → ℝ) → ℝ) (φ : (Fin d → ℝ) → (Fin d → ℝ))
    (h : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) where
  /-- the tangential dimension -/
  t : ℕ
  /-- the normal dimension minus one -/
  n : ℕ
  /-- the splitting into tangential and normal coordinates -/
  σ : Fin t ⊕ Fin (n + 1) ≃ Fin d
  /-- the phase exponents -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ j, 0 < k j
  /-- the centre has vanishing normal coordinates -/
  y₀_nIdx : ∀ j, y₀ (nIdx σ j) = 0
  /-- an open neighbourhood of the origin (translated coordinates) -/
  V₀ : Set (Fin d → ℝ)
  V₀_open : IsOpen V₀
  zero_mem : (0 : Fin d → ℝ) ∈ V₀
  /-- the analytic positive phase unit -/
  unit₀ : (Fin d → ℝ) → ℝ
  unit₀_analytic : AnalyticOnNhd ℝ unit₀ V₀
  unit₀_pos : ∀ y ∈ V₀, 0 < unit₀ y
  phase_eq : ∀ y ∈ V₀, K (φ (y + y₀)) = unit₀ y * ∏ j, y (nIdx σ j) ^ (2 * k j)
  /-- the analytic positive Jacobian unit -/
  jac₀ : (Fin d → ℝ) → ℝ
  jac₀_analytic : AnalyticOnNhd ℝ jac₀ V₀
  jac₀_pos : ∀ y ∈ V₀, 0 < jac₀ y
  /-- the tangential Jacobian weights (the Jacobian exponents of the tangential coordinates
  vanishing at the centre, whose phase exponent is zero) -/
  hT : Fin t → ℕ
  det_eq : ∀ y ∈ V₀, |(fderiv ℝ φ (y + y₀)).det| =
    jac₀ y * (∏ j, |y (nIdx σ j)| ^ h (nIdx σ j)) * ∏ i, |y (tIdx σ i)| ^ hT i
  /-- the Jacobian monomial does not vanish off the normal and weight hyperplanes -/
  monomialEval_ne_zero : ∀ y ∈ V₀, (∀ j, y (nIdx σ j) ≠ 0) →
    (∀ i, 0 < hT i → y (tIdx σ i) ≠ 0) → monomialEval (y + y₀) h ≠ 0

```

```lean
-- Grammar/ScalarChartNormalForm.lean
theorem phase_scalarNormalForm
    (hK : ∀ p ∈ S, K (planeSplit (stratumSplit I hne) p) =
      u (planeSplit (stratumSplit I hne) p) * monomialEval (planeSplit (stratumSplit I hne) p) e)
    (hind : ∀ p ∈ S, u (planeSplit (stratumSplit I hne) p) = tangentialUnit I hne u p.1)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a) {p} (hp : p ∈ S) :
    K (planeSplit (stratumSplit I hne) p) =
      scalarPhase I hne u e p.1 * ∏ a, p.2 a ^ (2 * normalHalfExp I hne e a) := by
```

```lean
-- Grammar/ScalarUnitKernel.lean
theorem hasLeadingTerm_integral_scalarBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hq : Continuous q) (hq_pos : ∀ z ∈ T, 0 < q z) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * scalarBoxKernel n h k b q A z N)
      (∫ z in T, βw z * scalarBoxFaceCoeff n h k b q A l z) l
      (multCount (ratioExp h k) l - 1) := by
```

```lean
-- Grammar/ScalarUnitKernel.lean
noncomputable def scalarBoxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
```

```lean
-- Grammar/SymmetricScalarUnitCells.lean
structure ScalarUnitCell (t : ℕ) where
  /-- The normal dimension is `n + 1`. -/
  n : ℕ
  /-- The density exponents. -/
  h : Fin (n + 1) → ℕ
  /-- The half phase exponents. -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- The box side. -/
  b : ℝ
  b_pos : 0 < b
  /-- The amplitude. -/
  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  A_cont : Continuous (Function.uncurry A)
  /-- The tangential base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The tangential weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_int : IntegrableOn βw base
  /-- The scalar phase unit. -/
  q : (Fin t → ℝ) → ℝ
  q_cont : Continuous q
  q_pos : ∀ z ∈ base, 0 < q z

```

```lean
-- Grammar/ProductChartHypotheses.lean
structure ProductMonomialChart {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
    (K : (Fin d → ℝ) → ℝ) where
  /-- The phase exponents. -/
  e : Fin d →₀ ℕ
  /-- The Jacobian exponents. -/
  h : Fin d →₀ ℕ
  /-- The open monomial neighbourhood of the domain. -/
  W : Set (Fin d → ℝ)
  W_open : IsOpen W
  dom_subset : (R.chart i).dom ⊆ W
  /-- hironaka's monomial-chart certificate (its existential units are not the ones below). -/
  monomial : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W
  /-- The phase unit (a specific witness, carrying the independence hypothesis below). -/
  u : (Fin d → ℝ) → ℝ
  u_cont : ContinuousOn u W
  u_ne : ∀ y ∈ W, u y ≠ 0
  phase_eq : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e
  /-- The Jacobian unit. -/
  v : (Fin d → ℝ) → ℝ
  v_cont : ContinuousOn v W
  det_eq : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h
  /-- The compact inactive base. -/
  T : Set (Fin d → ℝ)
  T_compact : IsCompact T
  T_nonempty : T.Nonempty
  T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  /-- The normal radius. -/
  b : ℝ
  b_pos : 0 < b
  dom_eq : (R.chart i).dom = productDom e.support T b
  unit_indep : ∀ y ∈ (R.chart i).dom, u y = u (zeroOn e.support y)
  /-- The inactive factor of the cover weight. -/
  r : (Fin d → ℝ) → ℝ
  r_meas : Measurable r
  /-- A bound of the weight factor. -/
  Cr : ℝ
  r_bound : ∀ x, |r x| ≤ Cr
  weight_eq : ∀ y ∈ (R.chart i).dom, R.weight i ((R.chart i).Φ y) = r (zeroOn e.support y)

```

```lean
-- Grammar/ResolutionTransport.lean
noncomputable def coverWeight (A : ι → Set X) (i : ι) (x : X) : ℝ :=
```

```lean
-- Grammar/MixedExponentExample.lean
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in SquareExample.box, Real.exp (-N * K y)) ~[atTop]
      fun N => 2 * Real.Gamma (1 / 4) * N ^ (-(1 / 4 : ℝ)) := by
```

```lean
-- Grammar/MixedExponentPosterior.lean
theorem tendsto_posteriorExpectation_sq :
    Tendsto ((ResolutionCover.ofChart chart).posteriorExpectation K one Fsq) atTop (𝓝 (1 / 5)) := by
```

```lean
-- Grammar/ResidualFaceCoefficient.lean
theorem reflected_coeff_eq (σ : Fin (c.n + 1) → Bool) :
    (c.reflected σ).coeff = ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) *
      (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
          (residualExponent c.h c.k c.lam a + 1)) *
        (faceLeadConst c.h c.k c.lam 1 *
          ∫ u in unitBox (c.n + 1),
            c.A z (reflect σ (c.b • faceProj c.h c.k c.lam u)) *
              residualWeight c.h c.k c.lam u))) := by
```

```lean
-- Grammar/ProductChartPosterior.lean
theorem tendsto_posteriorExpectation_of_productCharts (hact : (R.activeCoords Ps).Nonempty)
    {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
    (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact) ∧
      (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact)
          (R.coverDeg Ps hact) /
          R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact))) :=
```

```lean
-- strip normalisation (grep)
Grammar/StripBoxExpansion.lean:67:theorem exists_stripData {i : Fin d} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
Grammar/StripBoxExpansion.lean-68-    {ρ : (Fin d → ℝ) → ℝ} (hρ : AnalyticOnNhd ℝ ρ V) (hρpos : ∀ y ∈ V, 0 < ρ y)
Grammar/StripBoxExpansion.lean-69-    {Q₀ : Set (Fin d → ℝ)} (hQ₀ : IsCompact Q₀) (hQ₀V : Q₀ ⊆ V) (hQ₀i : ∀ y ∈ Q₀, y i = 0) :
Grammar/StripBoxExpansion.lean-70-    Nonempty (StripData i V ρ Q₀) := by
Grammar/StripBoxExpansion.lean-71-  obtain ⟨b₀, b, S, hb₀, hb, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩ :=
Grammar/StripBoxExpansion.lean-72-    exists_stripNormalisation hV hρ hρpos hQ₀ hQ₀V hQ₀i
Grammar/StripBoxExpansion.lean-73-  exact ⟨⟨b₀, b, hb₀, hb, S, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩⟩
--
Grammar/MonomialUnitRemoval.lean:87:noncomputable def unitRoot (β : ℝ) (m : ℕ) (u : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
Grammar/MonomialUnitRemoval.lean-88-  Real.exp (Real.log (u y / β) / m)
Grammar/MonomialUnitRemoval.lean-89-
Grammar/MonomialUnitRemoval.lean-90-theorem unitRoot_pos (β : ℝ) (m : ℕ) (u : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
Grammar/MonomialUnitRemoval.lean-91-    0 < unitRoot β m u y := Real.exp_pos _
Grammar/MonomialUnitRemoval.lean-92-
Grammar/MonomialUnitRemoval.lean-93-theorem unitRoot_pow {β : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) {u : (Fin d → ℝ) → ℝ}
--
Grammar/MonomialUnitRemoval.lean:99:theorem analyticAt_unitRoot {β : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) {u : (Fin d → ℝ) → ℝ}
Grammar/MonomialUnitRemoval.lean-100-    {y : Fin d → ℝ} (hu : AnalyticAt ℝ u y) (hpos : 0 < u y) : AnalyticAt ℝ (unitRoot β m u) y := by
Grammar/MonomialUnitRemoval.lean-101-  have h1 : AnalyticAt ℝ (fun y => u y / β) y := hu.div analyticAt_const hβ.ne'
Grammar/MonomialUnitRemoval.lean-102-  have hlog : AnalyticAt ℝ Real.log (u y / β) := analyticAt_log (div_pos hpos hβ)
Grammar/MonomialUnitRemoval.lean-103-  have h2 : AnalyticAt ℝ (fun y => Real.log (u y / β)) y :=
Grammar/MonomialUnitRemoval.lean-104-    AnalyticAt.comp (g := Real.log) (f := fun y => u y / β) hlog h1
Grammar/MonomialUnitRemoval.lean-105-  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
--
Grammar/StripBoxExpansion.lean:67:theorem exists_stripData {i : Fin d} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
Grammar/StripBoxExpansion.lean-68-    {ρ : (Fin d → ℝ) → ℝ} (hρ : AnalyticOnNhd ℝ ρ V) (hρpos : ∀ y ∈ V, 0 < ρ y)
Grammar/StripBoxExpansion.lean-69-    {Q₀ : Set (Fin d → ℝ)} (hQ₀ : IsCompact Q₀) (hQ₀V : Q₀ ⊆ V) (hQ₀i : ∀ y ∈ Q₀, y i = 0) :
Grammar/StripBoxExpansion.lean-70-    Nonempty (StripData i V ρ Q₀) := by
Grammar/StripBoxExpansion.lean-71-  obtain ⟨b₀, b, S, hb₀, hb, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩ :=
Grammar/StripBoxExpansion.lean-72-    exists_stripNormalisation hV hρ hρpos hQ₀ hQ₀V hQ₀i
Grammar/StripBoxExpansion.lean-73-  exact ⟨⟨b₀, b, hb₀, hb, S, hSopen, hSV, hcyl, hinj, hjac, himg, hcylimg, hinv⟩⟩

```
