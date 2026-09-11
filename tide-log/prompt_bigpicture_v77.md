# Consult #77 — grammar Lean: after the #76 plan (A, B, bridge, E, D all landed), the next programme

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
536 modules, axiom-clean). Your consults #74–#76 designed the resolved-space and adapted-density
programmes; every unit you proposed in #76 is landed. This consult asks for the next programme.

## Landed since #76 (exact statements in the appendix)

* CCXXXI `ScalarUnitKernel` (A): `HasLeadingTerm.comp_mul_const` (positive time change, coefficient
  `a^{−λ}c`), `scalarBoxKernel := boxKernel … 1 b A z (N * q z)`, `hasLeadingTerm_scalarBoxKernel`
  (no continuity of q), `abs_scalarBoxKernel_le` (comparison with the constant-unit kernel of the lower
  bound q₀ and |A|), `eventually_abs_scalarBoxKernel_div_le`, `hasLeadingTerm_integral_scalarBoxKernel`
  (q continuous, positive on the compact base).
* CCXXXII `SymmetricScalarUnitCells` (B): `integral_piBox_dilation`, `symScalarKernel_eq_sum`
  (two-sided box with `∏|u|^h` = Σ over 2^{n+1} orthants of positive-cube kernels of the reflected
  amplitudes), `ScalarUnitCell`, `FiniteScalarUnitAtlas`, `hasLeadingTerm_of_extremal`,
  `ScalarUnitCell.symAtlas` (orthant atlas of a symmetric cell; integrability from the uniform kernel
  bound `abs_scalarBoxKernel_le_const`), `hasLeadingTerm_boltzmannIntegral_of_scalarAtlases`.
* CCXXXIII `AdaptedPieceAtlas` (bridge): `pieceIntegral_eq_symIntegral` — an adapted piece
  (CCXXVIII) with compact base, integrable β, ε-ball normal box and pointwise scalar normal form
  (`amp·F∘φ = A∏|n|^h`, `K∘Φ = q(z)∏n^{2k}`) has piece integral = symmetric integral of the cell;
  `pieceAtlas : FiniteScalarUnitAtlas (d − |I|) (pieceIntegral …)`, `pieceAtlas_cell_lam`;
  `hasLeadingTerm_boltzmannIntegral_of_scalarAtlases'` with per-piece base dimension.
* CCXXXIV `FaceCoefficient` (E): `HasLeadingTerm.coeff_unique`, `PairDominates.total`,
  `HasLeadingTerm.pair_unique` (nonzero certificates identify the pair),
  `FiniteScalarUnitAtlas.tiedCoeff_eq` (decomposition-independence), all-minimal face formula
  `amplitudeCoeff = faceLeadConst·η(0)`, `faceLeadConst = Γ(λ)β^{−λ}/(d−1)!∏1/(2k_j)`,
  `ScalarUnitCell.coeff_of_all_minimal` (explicit face integral
  `b^{Σh+n+1}(b^{2Σk})^{−λ}·Γ(λ)/n!∏1/(2k_j)·∫_base β_w q^{−λ} A(·,0)`).
* CCXXXV `MomentKernel` (D): `boxKernel_shift` (u^α insertion = h ↦ h+α), `momentKernel`,
  `hasLeadingTerm_momentKernel` (shifted pair), `minRatio_le_minRatio_shift`,
  `HasLeadingTerm.div` (certificate ratios, k₂ ≤ k₁, c₂ ≠ 0), `hasLeadingTerm_normalisedMoment`.

## Where the theory now stands

The paper's Theorem (thm:expectation_expansion) is formalised as: (i) exact chart–stratum
decomposition of the resolved integral (CCXXIV), (ii) divisor-free pieces negligible (CCXXVI),
(iii) a conditional leading-term theorem whose hypothesis is a finite scalar-unit atlas for every
nonempty chart–stratum piece (CCXXX/CCXXXII/CCXXXIII), (iv) the first concrete constructor of such an
atlas — an adapted piece in scalar normal form (CCXXXIII), (v) the explicit face coefficient in the
all-minimal case and decomposition-independence (CCXXXIV), (vi) Mellin scaling of normal moments on
model cells (CCXXXV). Unconditional results elsewhere: the identified exponent pair (CCV, CCVIII,
CCIX) and the local chart theorem with an existential region.

Open gaps I see:
(G1) Extraction of the scalar normal form from a hironaka monomial chart with a unit independent of
     the normal coordinates: `K∘φ = u(z)·∏_{j∉I}z_j^{e_j}·∏_{j∈I}n_j^{e_j}` with e_j even on I
     (`even_positive_form_halfExp`?) and `|det Dφ| = |v(z,n)|∏|n|^h` — the amplitude `A(z,n) =
     |v(z,n)| p(φ) F(φ)` is then continuous if v, p∘φ, F∘φ are, and q(z) = u(z)∏_{j∉I}z_j^{e_j} is
     continuous and positive on the compact base (|z_j| ≥ ε). Also the fibre-constant allocation
     hypothesis (CCXXVIII) must be supplied or replaced.
(G2) An n-dependent unit u(z,n) (option C of #76: parametrised strip normalisation; image = a
     variable strip, not a cube; you advised deferring).
(G3) Symmetric (signed) moments and the identification of the model-cell moments with the tube fibre
     measures `condTubeNormalMeasure` of CCXVIII (requires an explicit equality of measures/densities
     on a cell).
(G4) The full expansion (all orders) on cells: the library has `CutoffExpansion`/
     `AnalyticCoreDecomposition.cutoffExpansion` for analytic amplitudes with the polydisc/coefficient
     -family class; a cell version with continuous amplitude gives only the leading term.
(G5) The §4 statistical transfer of the identified pair to the empirical/posterior objects (Astra #71
     (iv)); the fluctuation function machinery exists at the population level.
(G6) Positivity: `coeff > 0` for nonnegative β_w, q > 0 and A(z,0) > 0 on a positive-measure part of
     the base (the paper's positive leading coefficient); ties/cancellation across (i,I) handled by
     the signed sums.

## Questions

Q1. Rank G1–G6 (and anything I am missing) for the next 3–5 units; reasons (value for the paper,
    honesty, feasibility with the existing library).
Q2. For your top-ranked item give module contracts in the style of #74–#76 (statements, hypotheses,
    declarations to reuse, pitfalls). If G1: be precise about (a) how to get even exponents on the
    normal coordinates from K ≥ 0 (what `even_positive_form_halfExp` in the library gives — see
    appendix), (b) how to handle the fibre-constant allocation hypothesis honestly (state it, or prove
    it for a single chart cover where ρ ≡ 1 and dom is a product?), (c) the base as the compact
    tangential projection of dom intersected with the foot condition.
Q3. Is there a cheaper unconditional theorem available now? E.g. for a SINGLE monomial chart whose
    domain is a product box centred on a divisor point and whose unit is normal-independent, the
    full (all strata) leading term via atlases — is that honest and reachable?
Q4. Anything mis-stated in CCXXXI–CCXXXV from the appendix statements?

## Appendix: exact statements
105:theorem hasLeadingTerm_scalarBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
106-    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
107-    (hA : Continuous (Function.uncurry A)) {z : Fin t → ℝ} (hqz : 0 < q z) :
108-    HasLeadingTerm (scalarBoxKernel n h k b q A z) (scalarBoxFaceCoeff n h k b q A l z) l
109-      (multCount (ratioExp h k) l - 1) :=
110-  (hasLeadingTerm_boxKernel A hk one_pos hb hmin hatt hA z).comp_mul_const hqz
111-
112-theorem measurableSet_piBox_Ioc_pos : MeasurableSet (piBox (n + 1) (Ioc (0 : ℝ) b)) :=
113-  MeasurableSet.univ_pi fun _ => measurableSet_Ioc
--
177:theorem hasLeadingTerm_integral_scalarBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
178-    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
179-    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
180-    (hq : Continuous q) (hq_pos : ∀ z ∈ T, 0 < q z) {βw : (Fin t → ℝ) → ℝ}
181-    (hβw : IntegrableOn βw T) :
182-    HasLeadingTerm (fun N => ∫ z in T, βw z * scalarBoxKernel n h k b q A z N)
183-      (∫ z in T, βw z * scalarBoxFaceCoeff n h k b q A l z) l
184-      (multCount (ratioExp h k) l - 1) := by
185-  rcases T.eq_empty_or_nonempty with hT0 | hne

131:theorem symScalarKernel_eq_sum (hb : 0 < b) (hA : Continuous (Function.uncurry A))
132-    (z : Fin t → ℝ) (N : ℝ) :
133-    symScalarKernel n h k b q A z N =
134-      ∑ σ : Fin (n + 1) → Bool, scalarBoxKernel n h k b q (reflectAmp n A σ) z N := by
135-  have hAz : Continuous (A z) := continuous_amp_of_uncurry A hA z
136-  set G : (Fin (n + 1) → ℝ) → ℝ := fun u =>
137-    A z u * (∏ i, |u i| ^ h i) * Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i))) with hG
--
215:structure ScalarUnitCell (t : ℕ) where
216-  /-- The normal dimension is `n + 1`. -/
217-  n : ℕ
218-  /-- The density exponents. -/
219-  h : Fin (n + 1) → ℕ
220-  /-- The half phase exponents. -/
221-  k : Fin (n + 1) → ℕ
--
375:noncomputable def symAtlas : FiniteScalarUnitAtlas t c.symIntegral where
376-  ι := Fin (c.n + 1) → Bool
377-  cell := c.reflected
378-  eq := fun _ hN => c.symIntegral_eq_sum hN
379-
380-end ScalarUnitCell
381-

110:theorem pieceIntegral_eq_symIntegral {N : ℝ} (hN : 0 ≤ N) :
111-    R.pieceIntegral D ε i I F K p N =
112-      (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).symIntegral N := by
113-  rw [R.pieceIntegral_eq_adapted i D I hne Ad hFm hF hK hK0 hN]
114-  unfold ScalarUnitCell.symIntegral
115-  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
116-  congr 1
--
133:noncomputable def pieceAtlas :
134-    FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p) where
135-  ι := Fin (I.card - 1 + 1) → Bool
136-  cell := (R.pieceCell i D hε I hne Ad hbase hβ h k hk q hq hq_pos A hA).reflected
137-  eq := fun N hN => by
138-    rw [R.pieceIntegral_eq_symIntegral i D hε I hne Ad hbase hβ hbox h k hk q hq hq_pos A hA hamp
139-      hphase hFm hF hK hK0 hN]
variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (q : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ) (hq : Continuous q) (hq_pos : ∀ z ∈ Ad.base, 0 < q z)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))

72:theorem HasLeadingTerm.pair_unique (h₁ : HasLeadingTerm Z c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
73-    (h₂ : HasLeadingTerm Z c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) : lam₁ = lam₂ ∧ k₁ = k₂ := by
74-  by_contra hne
75-  have hne' : lam₁ ≠ lam₂ ∨ k₁ ≠ k₂ := by
76-    rcases not_and_or.1 hne with h | h
77-    · exact Or.inl h
78-    · exact Or.inr h
79-  rcases PairDominates.total hne' with hd | hd
80-  · exact hc₁ (h₁.coeff_unique (h₂.of_dominated hd))
--
87:theorem FiniteScalarUnitAtlas.tiedCoeff_eq {t₁ t₂ : ℕ} {Z : ℝ → ℝ}
88-    (A₁ : FiniteScalarUnitAtlas t₁ Z) (A₂ : FiniteScalarUnitAtlas t₂ Z) (lam₀ : ℝ) (k₀ : ℕ)
89-    (h₁ : ∀ i, lam₀ ≤ (A₁.cell i).lam)
90-    (h₁' : ∀ i, (A₁.cell i).lam = lam₀ → (A₁.cell i).mult - 1 ≤ k₀)
91-    (h₂ : ∀ i, lam₀ ≤ (A₂.cell i).lam)
92-    (h₂' : ∀ i, (A₂.cell i).lam = lam₀ → (A₂.cell i).mult - 1 ≤ k₀) :
93-    ∑ i ∈ A₁.tied lam₀ k₀, (A₁.cell i).coeff = ∑ i ∈ A₂.tied lam₀ k₀, (A₂.cell i).coeff :=
94-  (A₁.hasLeadingTerm_of_extremal lam₀ k₀ h₁ h₁').coeff_unique
95-    (A₂.hasLeadingTerm_of_extremal lam₀ k₀ h₂ h₂')
--
165:theorem ScalarUnitCell.coeff_of_all_minimal {t : ℕ} (c : ScalarUnitCell t)
166-    (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
167-    c.coeff = c.b ^ (∑ i, c.h i + (c.n + 1)) * (c.b ^ (2 * ∑ i, c.k i)) ^ (-c.lam) *
168-      (Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k i : ℝ))) *
169-        ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
170-  unfold ScalarUnitCell.coeff
171-  have hconst : faceLeadConst c.h c.k c.lam 1 =
172-      Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k i : ℝ)) := by
173-    rw [faceLeadConst_of_all_minimal c.h c.k c.lam 1 hall, Real.one_rpow, mul_one,

90:theorem hasLeadingTerm_momentKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
91-    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) :
92-    HasLeadingTerm (momentKernel n h k β b A α z)
93-      (boxFaceCoeff n (fun i => h i + α i) k β b A (minRatio (fun i => h i + α i) k) z)
94-      (minRatio (fun i => h i + α i) k)
95-      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) := by
96-  have hcert := hasLeadingTerm_boxKernel A hk hβ hb (minRatio_le (fun i => h i + α i) k)
97-    (exists_ratioExp_eq_minRatio (fun i => h i + α i) k) hA z
98-  unfold momentKernel
99-  refine hcert.congr' (Eventually.of_forall fun N => ?_)
100-  exact boxKernel_shift n h k β b A α z N
--
120:theorem HasLeadingTerm.div {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ} (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
121-    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) (hk : k₂ ≤ k₁) :
122-    HasLeadingTerm (fun N => Z₁ N / Z₂ N) (c₁ / c₂) (lam₁ - lam₂) (k₁ - k₂) := by
123-  have h := Tendsto.div h₁ h₂ hc₂
124-  refine h.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
125-  simp only [Pi.div_apply]
126-  rw [div_div_div_comm, powLogScale_div_powLogScale hN hk]
127-
128-end Ratio
129-
130-/-- **Normalised moments**: if the partition kernel has a nonzero coefficient and the log
--
133:theorem hasLeadingTerm_normalisedMoment {n : ℕ} {h k : Fin (n + 1) → ℕ} {β b : ℝ} {t : ℕ}
134-    {A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
135-    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ)
136-    (hc : boxFaceCoeff n h k β b A (minRatio h k) z ≠ 0)
137-    (hdeg : multCount (ratioExp h k) (minRatio h k) - 1 ≤
138-      multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) :
139-    HasLeadingTerm (fun N => momentKernel n h k β b A α z N / boxKernel n h k β b A z N)
140-      (boxFaceCoeff n (fun i => h i + α i) k β b A (minRatio (fun i => h i + α i) k) z /
141-        boxFaceCoeff n h k β b A (minRatio h k) z)
142-      (minRatio (fun i => h i + α i) k - minRatio h k)
143-      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1 -

Grammar/CentredChart.lean:37:theorem even_positive_form_halfExp {W : Set (Fin d → ℝ)} (hW : IsOpen W) {K u : (Fin d → ℝ) → ℝ}
Grammar/CentredChart.lean-38-    {e : Fin d →₀ ℕ} (hu : AnalyticOnNhd ℝ u W) (hu0 : ∀ y ∈ W, u y ≠ 0)
Grammar/CentredChart.lean-39-    (hK : ∀ y ∈ W, K y = u y * monomialEval y e) (hK0 : ∀ y ∈ W, 0 ≤ K y) {y₀ : Fin d → ℝ}
Grammar/CentredChart.lean-40-    (hy₀ : y₀ ∈ W) :
Grammar/CentredChart.lean-41-    ∃ W' : Set (Fin d → ℝ), IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧
Grammar/CentredChart.lean-42-      AnalyticOnNhd ℝ (reducedUnit u e y₀) W' ∧ (∀ y ∈ W', 0 < reducedUnit u e y₀ y) ∧
Grammar/CentredChart.lean-43-      ∀ y ∈ W', K y = reducedUnit u e y₀ y * ∏ j, y j ^ (2 * halfExp e y₀ j) := by
Grammar/CentredChart.lean-44-  have hcont : ContinuousAt u y₀ := (hu y₀ hy₀).continuousAt
Grammar/CentredChart.lean-45-  have heven : ∀ j, y₀ j = 0 → Even (e j) := fun j hj =>
Grammar/CentredChart.lean-46-    even_exponent_of_nonneg hW hK hK0 hy₀ hcont (hu0 y₀ hy₀) hj
Grammar/CentredChart.lean-47-  refine ⟨W ∩ (reducedUnit u e y₀) ⁻¹' Ioi 0, ?_, ⟨hy₀, reducedUnit_pos hW hK hK0 hy₀ hcont
Grammar/CentredChart.lean-48-    (hu0 y₀ hy₀)⟩, inter_subset_left, ?_, fun y hy => hy.2, fun y hy => ?_⟩
Grammar/CentredChart.lean-49-  · exact (continuousOn_reducedUnit e y₀ hu.continuousOn).isOpen_inter_preimage hW isOpen_Ioi
Grammar/CentredChart.lean-50-  · exact fun y hy => analyticAt_reducedUnit e y₀ (hu y hy.1)
Grammar/CentredChart.lean-51-  · rw [hK y hy.1, ← reducedUnit_mul_monomialEval u e y₀ y,

219:noncomputable def adaptedProductDensity_of_fibreConstant (β : (Fin d → ℝ) → ℝ)
220-    (hfc : (fun y => (sizePiece (D i) ε I).indicator (R.allocation i) y) =ᵐ[volume]
221-      fun y => (sizePiece (D i) ε I).indicator (fun y => β (planeFoot (stratumSplit I hne) y)) y) :
222-    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
223-      (sizePiece (D i) ε I) where
224-  base := {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I}
225-  measurableSet_base := (measurableSet_footCondition (D i) I).preimage
226-    ((planeSplit (stratumSplit I hne)).continuous.comp
227-      (continuous_id.prodMk continuous_const)).measurable
