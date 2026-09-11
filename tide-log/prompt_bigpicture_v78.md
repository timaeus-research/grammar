# Consult #78 — grammar Lean: the #77 plan is complete; what next?

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
541 modules, axiom-clean). Your #77 plan (five units) is fully landed. This consult asks for the next
programme.

## Landed since #77 (exact statements in the appendix)

* CCXXXVI `ScalarChartNormalForm` (unit 1): stratum coordinates `Ψ(z,n) = planeSplit (stratumSplit I) (z,n)`;
  `monomialEval_planeSplit` (monomial = tangential monomial × normal monomial), `abs_…` version;
  parity `normalExp_eq_two_mul_halfExp` from `even_exponent_of_nonneg` (needs y₀ ∈ W with y₀_j = 0 on I);
  `normalHalfExp_pos` (I active); `scalarPhase q(z) = u(Ψ(z,0))·tangentialMonomial(z)`,
  `phase_scalarNormalForm` (unit independent of normal coordinates on a region S),
  `scalarPhase_pos` (evaluate at n* = (ε/2,…)), `continuousOn_scalarPhase`.
* CCXXXVII `CompactProductChartDensity` (unit 2): `isClosed_footCondition`;
  `AdaptedProductDensity.restrictBase` (base ∩ T when the density vanishes off the fibres over T);
  `tangentialCarrier` (compact projection of dom); `compactFibreConstantDensity` with compact base;
  `fibreConstant_of_product` (fibre-saturated domain `y ∈ dom ↔ foot y ∈ T'` + fibre-constant cover
  weight ⇒ the fibre-constant hypothesis of CCXXVIII).
* CCXXXVIII `SingleChartScalarAtlas` (unit 3): Tietze `exists_continuous_extension_of_isClosed`;
  `chartPieceDensity` (restricted to fibres over T'; base compact); `mem_dom_of_mem_base(_closedBall)`;
  `pieceAmp = |v(Ψ)|·|tangential Jacobian monomial|·p(φΨ)·F(φΨ)`;
  **`exists_pieceAtlas_of_chart`**: for chart data (K∘φ = u·y^e, det Dφ = v·y^h on open W ⊇ dom,
  K ≥ 0, unit normal-independent on dom, closed T' with fibre-saturated dom and fibre-constant
  measurable bounded ρ_T, v/p∘φ/F∘φ continuous on W, a point of W vanishing on I) the piece integral
  has a `FiniteScalarUnitAtlas (d − |I|)` with all cells at `(minRatio (normalExp h) (normalHalfExp e), #min−1)`.
* CCXXXIX `PositiveScalarCoefficient` (unit 4): `box_prefactor_of_all_minimal` (= 1),
  `ScalarUnitCell.coeff_of_all_minimal'` (= faceConst · ∫_base βw q^{−λ} A(·,0)),
  `coeff_pos_of_all_minimal` (βw ≥ 0, A(·,0) ≥ 0 a.e., both > 0 on positive measure),
  `reflected_coeff_of_all_minimal`, `hasLeadingTerm_symIntegral` (2^{n+1}·coeff),
  `symIntegral_isEquivalent_of_all_minimal` (genuine `~` with c > 0), `FiniteScalarUnitAtlas.tiedCoeff_pos`.
* CCXL `LogRatioSymmetricMoments` (unit 5): `HasLeadingTerm.tendsto_div_ratio` (no log-degree order),
  `tendsto_div_mul_log` (dropping degree), `symMomentKernel_eq_sum` (orthant multiplier `orthantSign`),
  `hasLeadingTerm_symMomentKernel`.

## Where the paper's theorem stands
thm:expectation_expansion: (i) exact chart–stratum decomposition (CCXXIV), (ii) divisor-free pieces
negligible (CCXXVI), (iii) conditional leading term from per-piece scalar-unit atlases
(CCXXX/CCXXXII/CCXXXIII, per-piece base dimension), (iv) concrete constructor of a piece atlas from
monomial-chart data with product geometry + normal-independent unit (CCXXXVIII), (v) explicit face
coefficient and positivity in the all-minimal case (CCXXXIV/CCXXXIX), (vi) moments (CCXXXV/CCXL).
Not yet: an END-TO-END theorem combining (iii) and (iv) — i.e. `hasLeadingTerm_boltzmannIntegral_of_scalarAtlases'`
instantiated with `exists_pieceAtlas_of_chart` for every nonempty piece of every chart of a cover
(needs the per-chart product/unit hypotheses for all I, which for a single centred product chart with
unit independent of all active coordinates hold uniformly, as you noted in #77 Q2 B); the "cheapest
unconditional" whole-product-chart theorem (one symmetric cell) is also not written as a theorem about
`coverIntegral`; the identification `lam₀ = min over pieces` with a POSITIVE total coefficient is not
assembled.

## Candidates
(N1) End-to-end: `coverIntegral_hasLeadingTerm_of_productCharts` — a `ResolutionCover` all of whose
     charts are monomial with product geometry on every nonempty piece and units independent of all
     active coordinates ⇒ `Z_N[F] ` has the leading term at the extremal pair over (chart, stratum)
     with coefficient the sum of tied cell coefficients; plus positivity (F, p ≥ 0, > 0 somewhere)
     ⇒ genuine `~`. Bookkeeping-heavy but closes the loop; the hypotheses are strong (product
     geometry for ALL pieces of a chart — is that even consistent for a compact dom? A compact product
     box `T × [−b,b]^J` centred on the divisor works for I = J (full stratum); for I ⊊ J the piece
     `{|y_j| < ε for j ∈ I, ≥ ε for j ∈ J∖I}` ∩ dom is a product of T × annuli × ball — yes product-
     shaped, fibre-saturated ✓).
(N2) The single-chart whole-box theorem via one symmetric cell (no strata): `∫_{T×(−b,b)^J} …` as
     `ScalarUnitCell.symIntegral`; connect to `chartIntegral`/`coverIntegral` for a one-chart cover.
(N3) G2: n-dependent unit via a parametrised strip normalisation (you assessed: image is a variable
     strip; substantive).
(N4) G3: identify the model-cell moments with the tube fibre measures `condTubeNormalMeasure` of CCXVIII
     (equality of measures on a cell).
(N5) G4: all-orders expansion on cells with analytic amplitude (library has `AnalyticCoreDecomposition.cutoffExpansion`).
(N6) G5: §4 statistical transfer.
(N7) Consolidation/fidelity: an independent review pass (GPT) of CCXX–CCXL statements vs the paper
     (the project has a `tide-review` skill) and a mirror-remark cleanup.

Q1. Rank N1–N7 for the next 3–5 units; reasons.
Q2. For the top item, module contracts (statements, hypotheses, reuse, pitfalls). For N1 be explicit
    about: the hypothesis package per chart (a structure `ProductMonomialChart`?), how the per-piece
    T' and ρ_T are chosen (T' = the tangential product box? ρ_T from the cover weight), the choice of
    ε (common to all pieces; must be < b), and the extremal pair computation across (i, I).
Q3. Any mis-statement in CCXXXVI–CCXL from the appendix?

## Appendix
172-    exact R.mem_dom_of_mem_base i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn'
173-  have hcont : Continuous fun n : Fin (I.card - 1 + 1) → ℝ =>
174-      planeSplit (stratumSplit I hne) (z, n) :=
175-    (planeSplit (stratumSplit I hne)).continuous.comp (continuous_const.prodMk continuous_id)
176-  have hmem := mem_closure_image hcont.continuousAt hcl
177-  exact ((closure_mono himg).trans_eq (R.chart i).dom_compact.isClosed.closure_eq) hmem
178-
179-end ResolutionCover
180-
181-/-! ### The atlas from chart data -/
182-
183-namespace ResolutionCover
184-
185-variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
186-  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
187-  (e h : Fin d →₀ ℕ) (hD : D i = e.support) (hI : I ⊆ e.support)
188-  {K : (Fin d → ℝ) → ℝ} (hK0 : ∀ x, 0 ≤ K x) {W : Set (Fin d → ℝ)} (hW : IsOpen W)
189-  (hsub : (R.chart i).dom ⊆ W) (u v : (Fin d → ℝ) → ℝ) (hu : ContinuousOn u W)
190-  (hu0 : ∀ y ∈ W, u y ≠ 0) (hKu : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e)
191-  (hv : ContinuousOn v W)
192-  (hdet : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h)
193-  (hind : ∀ y ∈ (R.chart i).dom, u y = u (planeFoot (stratumSplit I hne) y))
194-  (T' : Set (Fin d → ℝ)) (hT' : IsClosed T') (ρT : (Fin d → ℝ) → ℝ) (hρm : Measurable ρT)
195-  {Cρ : ℝ} (hρb : ∀ x, |ρT x| ≤ Cρ)
196-  (hdom : ∀ y ∈ sizePiece (D i) ε I,
197-    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
198-  (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
199-    R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y))
200-  {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
201-  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) W)
202-  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) W)
203-  (hFm : Measurable F)
204-  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
205-  (hK : Measurable K) (hy₀ : ∃ y₀ ∈ W, ∀ j ∈ I, y₀ j = 0)
206-
208-noncomputable def pieceAmp (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ) :
209-    ℝ :=
210-  |v (planeSplit (stratumSplit I hne) (z, n))| * |tangentialMonomial I hne h z| *
211-    p.w ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) *
212-      F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))
213-
214-include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hind hT' hρm hρb hdom hρ hFc hpc hFm hF hK hy₀ in
216-pair `(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`. -/
217:theorem exists_pieceAtlas_of_chart :
217:theorem exists_pieceAtlas_of_chart :
218-    ∃ At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
219-      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
220-      ∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
221-        (minRatio (normalExp I hne h) (normalHalfExp I hne e)) := by
222-  -- the adapted density with compact base
223-  set Ad := R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ with hAd

103:theorem coeff_pos_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
104-    (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
105-    (hA : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.A z 0)
106-    (hpos : 0 < volume (c.base ∩ {z | 0 < c.βw z ∧ 0 < c.A z 0})) : 0 < c.coeff := by
107-  rw [c.coeff_of_all_minimal' hall]
108-  refine mul_pos c.faceConst_pos ?_
109-  have hbaseM : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
110-  have hnn : 0 ≤ᵐ[volume.restrict c.base] fun z => c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
111-    filter_upwards [hβ, hA, (ae_restrict_iff' hbaseM).2
--
161:theorem symIntegral_isEquivalent_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
162-    (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
163-    (hA : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.A z 0)
164-    (hpos : 0 < volume (c.base ∩ {z | 0 < c.βw z ∧ 0 < c.A z 0})) :
165-    0 < (2 : ℝ) ^ (c.n + 1) * c.coeff ∧
166-      c.symIntegral ~[atTop] fun N => (2 : ℝ) ^ (c.n + 1) * c.coeff *
167-        powLogScale c.lam (c.mult - 1) N := by
168-  have hc : 0 < (2 : ℝ) ^ (c.n + 1) * c.coeff :=
169-    mul_pos (by positivity) (c.coeff_pos_of_all_minimal hall hβ hA hpos)

40:theorem HasLeadingTerm.tendsto_div_ratio (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
41-    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
42-    Tendsto (fun N => (Z₁ N / Z₂ N) / (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N)) atTop
43-      (𝓝 (c₁ / c₂)) := by
44-  have h := Tendsto.div h₁ h₂ hc₂
45-  refine h.congr' (Eventually.of_forall fun N => ?_)
46-  simp only [Pi.div_apply]
47-  rw [div_div_div_comm]
48-
--
118:theorem hasLeadingTerm_symMomentKernel (hk : ∀ i, 0 < k i) (hb : 0 < b)
119-    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) {z : Fin t → ℝ} (hqz : 0 < q z) :
120-    HasLeadingTerm (symMomentKernel n h k b q A α z)
121-      (∑ σ : Fin (n + 1) → Bool, orthantSign n α σ *
122-        scalarBoxFaceCoeff n (fun i => h i + α i) k b q (reflectAmp n A σ)
123-          (minRatio (fun i => h i + α i) k) z)
124-      (minRatio (fun i => h i + α i) k)
125-      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) := by
126-  have hcell : ∀ σ : Fin (n + 1) → Bool, HasLeadingTerm

176:theorem hasLeadingTerm_boltzmannIntegral_of_scalarAtlases' (e h : ι → Fin d →₀ ℕ)
177-    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
178-    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
179-    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
180-    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
181-    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) (tdim : ι → Finset (Fin d) → ℕ)
182-    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
183-      FiniteScalarUnitAtlas (tdim i I) (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
184-    (lam₀ : ℝ) (k₀ : ℕ)
185-    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
186-      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
187-    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
188-      (j : (At i I hI hne).ι),
189-      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
190-    HasLeadingTerm (R.boltzmannIntegral F K p)
191-      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
192-        scalarAtlasPieceCoeff' At lam₀ k₀ i I) lam₀ k₀ := by
193-  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
194-    (scalarAtlasPieceCoeff' At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
195-    (fun i I hI => by
196-      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
197-      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
198-      unfold scalarAtlasPieceCoeff'
199-      rw [dif_pos ⟨hsub, hne⟩]
200-      exact (At i I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam i I hsub hne)

64:structure ResolutionChart (d : ℕ) where
65-  /-- the chart domain -/
66-  dom : Set (Fin d → ℝ)
67-  dom_compact : IsCompact dom
68-  /-- the chart map -/
69-  φ : (Fin d → ℝ) → (Fin d → ℝ)
70-  /-- an open neighbourhood of the domain on which the chart map is `C¹` -/
71-  U : Set (Fin d → ℝ)
72-  U_open : IsOpen U
73-  dom_subset : dom ⊆ U
74-  smooth : ContDiffOn ℝ 1 φ U
75-  /-- the exceptional set -/
76-  E : Set (Fin d → ℝ)
77-  E_subset : E ⊆ dom
78-  E_closed : IsClosed E
79-  E_null : volume E = 0
80-  inj : InjOn φ (dom \ E)
81-
82-namespace ResolutionChart
240:structure ResolutionCover (d : ℕ) (ι : Type*) [Fintype ι] where
241-  /-- the charts -/
242-  chart : ι → ResolutionChart d
243-
Grammar/CoverAssembly.lean:38:noncomputable def coverIntegral (F E : (Fin d → ℝ) → ℝ) : ℝ :=
Grammar/CoverAssembly.lean-39-  ∫ x in ⋃ i, R.image i, F x * Real.exp (E x)
Grammar/CoverAssembly.lean-40-
Grammar/CoverAssembly.lean-41-/-- The pullback of `F e^{E}` to chart `i`, against the weighted source measure, over `S`. -/
Grammar/ResolutionTransport.lean:249:def image (i : ι) : Set (Fin d → ℝ) := (R.chart i).φ '' (R.chart i).dom
Grammar/ResolutionTransport.lean-250-
Grammar/ResolutionTransport.lean-251-theorem isCompact_image (i : ι) : IsCompact (R.image i) :=
Grammar/ResolutionTransport.lean-252-  (R.chart i).dom_compact.image_of_continuousOn (R.chart i).continuousOn
--
Grammar/ResolutionTransport.lean:258:noncomputable def weight (i : ι) : (Fin d → ℝ) → ℝ := coverWeight R.image i
Grammar/ResolutionTransport.lean-259-
Grammar/ResolutionTransport.lean-260-theorem measurable_weight (i : ι) : Measurable (R.weight i) :=
Grammar/ResolutionTransport.lean-261-  measurable_coverWeight R.measurableSet_image i
--
Grammar/ResolutionTransport.lean:264:noncomputable def sourceMeasure (i : ι) : Measure (Fin d → ℝ) :=
Grammar/ResolutionTransport.lean-265-  (volume.restrict (R.chart i).dom).withDensity fun x =>
Grammar/ResolutionTransport.lean-266-    (R.chart i).absDet x * ENNReal.ofReal (R.weight i ((R.chart i).Φ x))
Grammar/ResolutionTransport.lean-267-
