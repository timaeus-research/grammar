# Consult #82 — grammar Lean: #81 units 1–3 landed; designing unit 4 (variable-unit product pieces) and the atlas generalisation

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
557 modules, axiom-clean, all `[propext, Classical.choice, Quot.sound]`). Your #81 programme (R2, the
normal-dependent phase unit, by UNIT-RANGE PARTITION): units 1–3 are landed exactly as specified; unit 4
(`VariableUnitProductPieces`) and unit 5 (regressions) remain. Before touching the chart–stratum assembly I
want your design decision on the atlas interface, because the assembly (CCXXXIII–CCLII, ~2200 lines across
seven modules) is written against `ScalarUnitCell`/`FiniteScalarUnitAtlas`, and `VarUnitCell` is (per your
#81 instruction) NOT a `ScalarUnitCell`.

## Landed since #81 (exact statements in the appendix)
* CCLIII `PositiveUnitRangePartition`: ramps `ramp c w s = max 0 (min 1 ((s−c)/w))`, telescoping partition of
  unity `chi a w j = G j − G (j+1)` with `∑_{j<m} chi j s = 1` for `s ≤ a + m w` (`sum_chi`), support bounds
  `lowerPt ≤ s < upperPt` where `chi ≠ 0`, `upperPt ≤ (1 + 2w/a) · lowerPt` (multiplicative width control),
  positive bounds of a positive continuous function on a compact set, and the approximate-squeeze lemma
  `hasLeadingTerm_of_approx_squeeze` (liminf/limsup within `(1±δ)`-factors for every δ ⇒ the limit).
* CCLIV `VariableUnitKernel`: `varBoxKernel n h k b u A z N = ∫_{(0,b]^{n+1}} A z v · ∏ v_i^{h_i} ·
  e^{−u(z,v) N ∏ v_i^{2k_i}}`; `varBoxFaceCoeff = boxFaceCoeff (β := 1) of A·u^{−l}` (the unit frozen on
  the minimal face by `faceProj`, residual coordinates kept); monotonicity in the unit for nonnegative
  amplitudes (`varBoxKernel_anti_unit`), additivity over amplitude sums, uniform bounds, measurability in the
  base point, integrability of `βw · varBoxKernel` over a compact base; face-coefficient additivity/monotonicity
  (`boxFaceCoeff_sum`, `boxFaceCoeff_mono`, `boxFaceCoeff_nonneg'`) with `ContinuousOn` hypotheses on the
  closed box (the frozen amplitude `A·u^{−l}` is only continuous where `u > 0`).
* CCLV `VariableUnitCertificate`: ★ `hasLeadingTerm_varBoxKernel` (pointwise in `z`, SIGNED continuous
  amplitude, positive continuous unit bounded in `[a, B]` on the closed box) and ★★
  `hasLeadingTerm_integral_varBoxKernel` (integrated against an integrable signed base weight over a compact
  base, by dominated convergence): `HasLeadingTerm (∫_T βw · varBoxKernel …) (∫_T βw · varBoxFaceCoeff … l)
  l (multCount − 1)`. Proof: partition the RANGE of `u` into pieces `A·chi_j(u)` of multiplicative width
  `≤ 1+δ`; sandwich each piece between constant-unit kernels (CCXXXI certificates, coefficients
  `(u_j^±)^{−l}·faceCoeff`); compare face coefficients; squeeze δ → 0; signed amplitudes by `A = A⁺ − A⁻`.
* CCLVI `SymmetricVariableUnitCells`: `symVarKernel` over the full box `(−b,b]^{n+1}` with `|v|^h` weights,
  `symVarKernel_eq_sum` (= ∑ over `2^{n+1}` orthant reflections of `varBoxKernel` with reflected `A` AND
  reflected `u`), `structure VarUnitCell t` (n h k k_pos b b_pos A A_cont base base_compact βw βw_int u
  u_cont u_pos-on-base×closedBall), `lam mult integral coeff hasLeadingTerm`, `reflected σ` (reflects A and u),
  `symIntegral`, `symIntegral_eq_sum`, ★ `hasLeadingTerm_symIntegral`, `reflected_coeff_eq` (the projected
  orthant residual formula with `A·u^{−λ}` on the face), `reflected_coeff_congr`, `sum_reflected_coeff`
  (`2^{|J|} ∑_{residual signs}`), and `ScalarUnitCell.toVar` with `toVar_integral`/`toVar_coeff` (constant-unit
  cells embed with the same integral and coefficient — your "compatibility under `unit_indep`" at cell level).

Mirror: the normal-dependent-unit paragraph carries dots for CCLV/CCLVI; its not-yet-formalised list now says:
"the insertion of variable-unit cells into the chart–stratum assembly (the product-chart theorem still assumes
the unit independent of the active coordinates); regular supplied cover weights; the subleading terms".

## How the current assembly consumes the atlas (this is the refactor surface)
1. `FiniteScalarUnitAtlas t Z := { ι, [Fintype ι], cell : ι → ScalarUnitCell t, eq : ∀ N ≥ 0, Z N = ∑ i,
   (cell i).integral N }`, `tied lam₀ k₀`, `hasLeadingTerm_of_extremal` (only uses `cell.lam/mult/coeff/
   hasLeadingTerm` and `eq`).
2. `AdaptedPieceAtlas`: `pieceCell` (the ScalarUnitCell of a piece in scalar normal form, hypotheses `hamp :
   Ad.amp z n · F(φΨ(z,n)) = A z n ∏|n_a|^{h_a}` and `hphase : K(ΦΨ(z,n)) = q z ∏ n_a^{2k_a}` on base × ball),
   `pieceIntegral_eq_symIntegral` (the piece integral IS `pieceCell.symIntegral`; proof: `pieceIntegral_eq_adapted`,
   pointwise `hphase/hamp` + `ring_nf`, `ball = piBox Ioo`, `Ioo =ᵐ Ioc`), `pieceAtlas` (orthant atlas =
   `(pieceCell).reflected`), and the generic global theorem `hasLeadingTerm_boltzmannIntegral_of_scalarAtlases'`
   (a `FiniteScalarUnitAtlas` per chart–stratum pair, dominated by `(lam₀,k₀)` ⇒ `HasLeadingTerm
   (boltzmannIntegral F K p) (∑_i ∑_I scalarAtlasPieceCoeff' At lam₀ k₀ i I) lam₀ k₀`).
3. `SingleChartScalarAtlas.exists_pieceAtlas_of_chart_data`: from monomial-chart data with `hind : ∀ y ∈ dom,
   u y = u (planeFoot y)` (normal-independence ON THE STRATUM), it proves the scalar normal form
   `K(ΦΨ(z,n)) = scalarPhase z · ∏ n_a^{2k_a}` with `scalarPhase z = tangentialUnit u z · tangentialMonomial e z`
   (unit at the foot × phase monomial of the active coordinates that were assigned to the base), positivity of
   `scalarPhase` on the base (from `K ≥ 0`, `u ≠ 0`), Tietze-extends `q'` (compact base) and `A' = pieceAmp`
   (base × closedBall) to continuous functions, and returns `At = R.pieceAtlas … q' … A' … hamp' hphase' …`
   (an EQUALITY of atlases, so consumers can `obtain ⟨…, rfl⟩` and read the cells).
4. `ProductChartHypotheses.ProductMonomialChart` (the hypothesis package; field `unit_indep : ∀ y ∈ dom,
   u y = u (zeroOn e.support y)`, from which `unit_indep_piece` gives `hind` for every stratum) →
   `ProductChartPieceData.exists_pieceAtlas` / `pieceAtlas'` (classical choice) → `ProductChartPositivity`
   (`IsPieceAtlasData`, `pieceAtlasD`, `cell_coeff_nonneg_of_data` via `ScalarUnitCell.coeff_nonneg (hβ hA)`,
   `exists_cell_coeff_pos_of_data`, `productCoeffD`, ★★ `boltzmannIntegral_isEquivalent_of_productCharts`) →
   `ProductChartPosterior` (★★ `tendsto_posteriorExpectation_of_productCharts`) → `ProductChartTiedStrata`
   (`productCoeffD_extremal_eq_sum_minimal` via `ScalarUnitCell.reflected_coeff_eq`, `pieceAtlas_sum_tied_residual`)
   → the examples (`OneChartProductExample`, `MixedExponentExample/Posterior`) which BUILD a `ProductMonomialChart`
   (with `unit_indep := …`) and compute `productCoeffD`.

## Questions

**Q1 (atlas interface).** Three options:
 (a) An abstract cell record `LeadingCell := { integral : ℝ → ℝ, coeff lam : ℝ, mult : ℕ, hasLeadingTerm }` with
     `FiniteLeadingAtlas Z := { ι, cell : ι → LeadingCell, eq }`, coercions `ScalarUnitCell.toLeading`,
     `VarUnitCell.toLeading`, `FiniteScalarUnitAtlas.toLeading`, and the generic global theorem restated once for
     `FiniteLeadingAtlas` (the old one becomes a one-line corollary). Positivity/tied-strata arguments that need
     the concrete cell fields stay on the concrete atlases (`pieceAtlas`-equality pattern of item 3).
 (b) A parallel `FiniteVarUnitAtlas` + `varPieceCell`/`varPieceAtlas` + `hasLeadingTerm_boltzmannIntegral_of_varAtlases'`,
     duplicating ~80 lines and leaving the scalar path untouched.
 (c) Redefine `ScalarUnitCell` as `VarUnitCell` with constant unit (breaking; touches every consumer).
 Which do you want, and why? My inclination is (b) for the leading-term theorem (fast, zero risk to landed
 theorems) with (a) deferred; but if you foresee the posterior/tied-strata layers needing to mix both cell kinds
 in ONE atlas (e.g. tied cells from scalar-form strata and variable-form strata of different charts), (a) is
 needed at once. Note `scalarAtlasPieceCoeff'` already quantifies over a per-pair atlas family `At i I hI hne`,
 so mixing kinds across pairs is only a matter of the coefficient function's type.

**Q2 (unit 4 contracts, precisely).** Proposed:
 (i) `phase_varNormalForm`: on the piece, `K(ΦΨ(z,n)) = q_var(z,n) · ∏ n_a^{2k_a}` with
     `q_var z n := u (Ψ(z,n)) · tangentialMonomial I hne e z` — NO `hind`. (The active base coordinates carry
     their phase monomial; the unit is evaluated at the actual point.)
 (ii) continuity of `q_var` on the closed piece (from `u_cont` on `W ⊇ dom`, `Ψ` continuous, and the closed
     piece ⊆ dom — the existing `mem_dom_of_mem_base_closedBall`); positivity on base × closedBall: `u ≠ 0` on
     `W`, `tangentialMonomial ≠ 0` on the base (the base of `chartPieceDensity`/`pieceDensity` already excludes
     foot points with vanishing tangential monomial?), and the SIGN from `K ≥ 0` at points with all `n_a ≠ 0`
     plus continuity. Is `u ≠ 0` + `K ≥ 0` enough, or should the package carry `u > 0` on `W` (hironaka's
     `exists_unit` gives `u ≠ 0`; on a connected `W` with `K ≥ 0`, `u > 0` follows — but `W` need not be connected)?
 (iii) `varPieceCell : VarUnitCell` from an adapted density + `hamp` + `hphase_var`, `pieceIntegral_eq_varSymIntegral`
     (same proof as item 2 with `u z v` replacing `q z`), `varPieceAtlas`.
 (iv) `exists_varPieceAtlas_of_chart_data` = item 3 without `hind` (Tietze extension of `q_var` from
     base × closedBall — `VarUnitCell.u_pos` is stated on exactly that set, by design).
 (v) `ProductMonomialChart'` := `ProductMonomialChart` minus `unit_indep` (or a `Prop`-valued flag?), the
     forgetful map, and `exists_varPieceAtlas` for it; then a NEW top-level
     `hasLeadingTerm_boltzmannIntegral_of_productChartsVar` (leading term with the variable-unit coefficients,
     nonnegativity via `boxFaceCoeff_nonneg'` — needs `A ≥ 0`, which is `F ≥ 0` — positivity of the extremal cell
     as in CCXLV) and ★★ `boltzmannIntegral_isEquivalent_of_productChartsVar`. Do you agree the identified-pair
     step (CCXLV's `exists_extremal_stratum` + positivity) transfers verbatim, since the coefficient
     `∫ β · boxFaceCoeff(A·u^{−λ})` is positive for the same reasons (positive continuous integrand on a set of
     positive measure)?
 (vi) The posterior theorem for variable units then follows from `tendsto_posteriorExpectation_of_hasLeadingTerm`
     with the two new leading terms — is anything else needed?
 Please confirm/correct the contract list and give the ORDER you want (I intend: (i)–(iv) as one unit, (v) as one
 unit, (vi) + tied-strata residual formula as one unit).

**Q3 (should `unit_indep` be removed or kept?).** Removing the field breaks the three examples (they supply
`unit_indep := …` trivially since `u = 1`). Options: keep `ProductMonomialChart` and add `ProductMonomialChart'`
without the field + `toVar`-style forgetful map (all old theorems intact, examples untouched, new theorems on the
primed structure); or delete the field and repair the examples (cleaner; one-off cost). Your call.

**Q4 (unit 5 regressions).** Confirm the predicted constants for the one-chart identity cover on `[−1,1]²`,
`(λ*, m*) = (1/4, 1)`, no log:
 * `K = (1+y²) x² y⁴` (unit `1+y²`, frozen on the face `y = 0` ⇒ 1): coefficient `2Γ(1/4)`;
 * `K = (1+x²+y²) x² y⁴`: `{0,1}`-piece `2^{|J|=1} · 2 residual signs · Γ(1/4)/4 · ∫₀¹ x^{−1/2}(1+x²)^{−1/4} dx
   = Γ(1/4) ∫₀¹ x^{−1/2}(1+x²)^{−1/4} dx`, `{1}`-piece null base at cutoff `ε = 1`;
 * `K = x² y⁴ z⁴` on `[−1,1]³`: `(1/4, 2)`, `~ c N^{−1/4} log N` — what is `c`? (my computation: minimal set
   `{1,2}`, `faceLeadConst = Γ(1/4)/((2−1)!) · (1/4)(1/4) = Γ(1/4)/16`, reflections `2^{2}`, residual `∫₀¹ x^{−1/2} = 2`,
   residual signs 2 ⇒ `4 · 2 · Γ(1/4)/16 · 2 = Γ(1/4)`; plus the tied strata `{0,1,2}` (all-minimal? no: `λ_0 = 1/2`
   so `0` is not minimal; the `{0,1,2}` piece has residual coordinate `x` and the `{1,2}` piece has null base at
   `ε = 1`). So `c = Γ(1/4)`?
 For the variable-unit examples the amplitude is `1`, the unit `u(x,y) = 1+y²` resp. `1+x²+y²`. Do you want the
 regressions BEFORE the assembly refactor (they exercise only `VarUnitCell` on a hand-built cell plus the
 one-chart cover of CCXLIX, if the piece bridge (ii)–(iv) exists) or after?

**Q5 (R3/R4 and priority).** After unit 4/5 you had R3 (supplied cover weights: regular partitions of unity
instead of the counting/factoring weights) and R4 (the dependency statement). Given "new theorems first", rank:
(A) unit 4 (i)–(vi) [removes `unit_indep` from the headline theorems], (B) unit 5 regressions, (C) R3, (D) the
Θ/expansion-level statements (subleading terms), (E) anything in the paper's §3–§4 you consider under-served by
the current 910 dots (the mirror's not-yet-formalised lists are the only remaining explicit gaps I know of).
Also: after (A), is there any remaining hypothesis of the product-chart theorem that a resolution does NOT deliver
(the centred product domain `productDom J T b`, the inactive base `T`, the cover weight factoring through the
inactive coordinates, the fixed cutoff `ε ≤ b`)? I want a precise statement of the distance from "every monomial
chart of a hironaka resolution" to "product chart package", for the scope remark and for planning R3/R4.

## Appendix — exact Lean statements
### CCLV VariableUnitCertificate
```lean
theorem hasLeadingTerm_varBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) {z : Fin t → ℝ}
    {a B : ℝ} (ha : 0 < a) (hab : ∀ v ∈ piBox (n + 1) (Icc 0 b), a ≤ u z v ∧ u z v ≤ B) :
    HasLeadingTerm (varBoxKernel n h k b u A z) (varBoxFaceCoeff n h k b u A l z) l
      (multCount (ratioExp h k) l - 1) := by

theorem hasLeadingTerm_integral_varBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hu : Continuous (Function.uncurry u))
    (hu_pos : ∀ z ∈ T, ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 < u z v) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * varBoxKernel n h k b u A z N)
      (∫ z in T, βw z * varBoxFaceCoeff n h k b u A l z) l (multCount (ratioExp h k) l - 1) := by
```

### CCLIV VariableUnitKernel (definitions)
```lean
noncomputable def varBoxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ v in piBox (n + 1) (Ioc 0 b),
    A z v * (∏ i, v i ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))

noncomputable def varBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  boxFaceCoeff n h k 1 b (fun z v => A z v * u z v ^ (-l)) l z
```

### CCLVI SymmetricVariableUnitCells
```lean
noncomputable def symVarKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ v in piBox (n + 1) (Ioc (-b) b),
    A z v * (∏ i, |v i| ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))

structure VarUnitCell (t : ℕ) where

noncomputable def integral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * varBoxKernel c.n c.h c.k c.b c.u c.A z N

noncomputable def coeff : ℝ :=
  ∫ z in c.base, c.βw z * varBoxFaceCoeff c.n c.h c.k c.b c.u c.A c.lam z

theorem hasLeadingTerm : HasLeadingTerm c.integral c.coeff c.lam (c.mult - 1) :=

noncomputable def symIntegral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * symVarKernel c.n c.h c.k c.b c.u c.A z N

theorem hasLeadingTerm_symIntegral :
    HasLeadingTerm c.symIntegral (∑ σ : Fin (c.n + 1) → Bool, (c.reflected σ).coeff) c.lam
      (c.mult - 1) := by

theorem reflected_coeff_eq (σ : Fin (c.n + 1) → Bool) :
    (c.reflected σ).coeff = ∫ z in c.base, c.βw z *
      (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
          (residualExponent c.h c.k c.lam a + 1)) *
        (faceLeadConst c.h c.k c.lam 1 *
          ∫ w in unitBox (c.n + 1),
            c.A z (reflect σ (c.b • faceProj c.h c.k c.lam w)) *
              c.u z (reflect σ (c.b • faceProj c.h c.k c.lam w)) ^ (-c.lam) *
              residualWeight c.h c.k c.lam w)) := by

theorem sum_reflected_coeff :
    ∑ σ, (c.reflected σ).coeff =
      2 ^ (minimalCoords c.h c.k c.lam).card *
        ∑ τ : {a : Fin (c.n + 1) // a ∉ minimalCoords c.h c.k c.lam} → Bool,
          (c.reflected (extendFalse _ τ)).coeff :=

theorem ScalarUnitCell.toVar_coeff {t : ℕ} (c : ScalarUnitCell t) : c.toVar.coeff = c.coeff := by
```

### The scalar atlas interface and its generic consumer
```lean
structure FiniteScalarUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where

noncomputable def tied (lam₀ : ℝ) (k₀ : ℕ) : Finset At.ι :=

theorem hasLeadingTerm_of_extremal (lam₀ : ℝ) (k₀ : ℕ) (hlam : ∀ i, lam₀ ≤ (At.cell i).lam)
    (hk : ∀ i, (At.cell i).lam = lam₀ → (At.cell i).mult - 1 ≤ k₀) :
    HasLeadingTerm Z (∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff) lam₀ k₀ := by

noncomputable def pieceCell : ScalarUnitCell (d - (I.card - 1 + 1)) where

theorem pieceIntegral_eq_symIntegral {N : ℝ} (hN : 0 ≤ N) :
    R.pieceIntegral D ε i I F K p N =
      (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).symIntegral N := by

noncomputable def pieceAtlas :
    FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) where

noncomputable def scalarAtlasPieceCoeff' {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    {tdim : ι → Finset (Fin d) → ℕ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=

theorem hasLeadingTerm_boltzmannIntegral_of_scalarAtlases' (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (tdim : ι → Finset (Fin d) → ℕ)
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι),
      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' At lam₀ k₀ i I) lam₀ k₀ := by
```

### The chart-data bridge (where normal-independence enters)
```lean
theorem unit_indep_piece (u : (Fin d → ℝ) → ℝ)
    (hind : ∀ y ∈ productDom J T b, u y = u (zeroOn J y)) (I : Finset (Fin d)) (hne : I.Nonempty)
    (hIJ : I ⊆ J) {y : Fin d → ℝ} (hy : y ∈ productDom J T b) :
    u y = u (planeFoot (stratumSplit I hne) y) := by

structure ProductMonomialChart {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
    (K : (Fin d → ℝ) → ℝ) where

noncomputable def scalarPhase (z : Fin (d - (I.card - 1 + 1)) → ℝ) : ℝ :=
```
`exists_pieceAtlas_of_chart_data` (SingleChartScalarAtlas.lean:220) takes `hind : ∀ y ∈ dom, u y = u (planeFoot (stratumSplit I hne) y)`, derives `hindS` on the piece, applies `phase_scalarNormalForm` (K∘Φ∘Ψ(z,n) = scalarPhase z * ∏ n_a^{2k_a}) and `scalarPhase_pos`, then Tietze-extends `q'` (from the compact base) and `A'` (from base × closedBall) to continuous functions, and returns `At = R.pieceAtlas … q' … A' … hamp' hphase' …` with `q' = scalarPhase` on the base and `A' = pieceAmp` on base × closedBall.