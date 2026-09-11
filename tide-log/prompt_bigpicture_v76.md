# Consult #76 — grammar Lean: after the conditional adapted-density theorem, what next?

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
531 modules, axiom-clean). Your consult #75 (design D′, six modules) has been executed as far as it can
be without new geometric constructions. This consult asks for the next direction.

## Landed since #75 (exact statements in the appendix)

* CCXXVI `DivisorFreePieces`: `hasLeadingTerm_pieceIntegral_empty_of_monomial` — on a hironaka monomial
  chart the divisor-free piece (all divisor coordinates ≥ ε) of the compact domain has phase ≥ δ > 0
  (`K∘φ = |u|·|y^e|`, `|u|` min on compact dom, `|y^e| ≥ ∏ ε^{e_j}`), hence is a leading-term
  certificate with coefficient 0 at every power–log scale; `hasLeadingTerm_boltzmannIntegral_of_monomial`
  (interface needs certificates only for NONEMPTY chart–stratum pieces).
* CCXXVII `IntegratedLeadingTerm` (module 3): `hasLeadingTerm_integral_of_dominated_kernel` — fibrewise
  certificates + eventual a.e. normalised domination + `|β_w|·G` integrable ⇒ integrated certificate.
* CCXXVIII `AdaptedPieceDensity` (module 1): `AdaptedProductDensity τ w piece` (a.e. factorisation
  `1_piece·w∘planeSplit = 1_base(z)β(z)·1_Q(n)a(z,n)`), `integral_piece_eq` (iterated form),
  `pieceIntegral_eq_adapted`, and `adaptedProductDensity_of_fibreConstant`: if a.e. on the piece the
  allocation `1_dom·(ρ_i∘Φ_i)` equals `β∘planeFoot`, the static density is adapted with base = foot
  condition, Q = ε-ball (two-sided!), amplitude `|det Dφ_i|·(p∘Φ_i)`.
* CCXXIX `ConstantUnitKernel` (module 2, constant-unit version): for the PRESCRIBED cube kernel
  `L_N(z) = ∫_{(0,b]^{n+1}} A(z,u) ∏u^h e^{−βN ∏u^{2k}} du` with jointly continuous `A`:
  `hasLeadingTerm_boxKernel` (pointwise, coefficient `b^{Σh+n+1}(b^{2Σk})^{−λ} amplitudeCoeff(A(z,b·))`),
  `eventually_abs_boxKernel_div_le` (∃ C, ∀ᶠ N, ∀ z ∈ T compact, |L_N(z)|/scale ≤ C — from the
  library's `tendstoUniformlyOn_normChart` (uniform convergence of the normalised unit-box chart
  integral on compact sets of `C(cube,ℝ)²` inputs), through `origPhaseIntegral_dilation` and the
  reparametrisation N ↦ √(N b^{2Σk}) of the chart variable), `hasLeadingTerm_integral_boxKernel`.
* CCXXX `ConstantUnitAtlas` (modules 4–6, conditional): `ConstantUnitCell` (compact base, integrable
  base weight, cube side b, exponents (h,k), constant unit β, continuous A), `FiniteConstantUnitAtlas Z`
  (finitely many cells with `∀ N ≥ 0, Z N = ∑ cell.integral N`), `hasLeadingTerm_of_extremal`,
  `hasLeadingTerm_boltzmannIntegral_of_atlases`: for a cover of monomial charts whose nonempty
  chart–stratum piece integrals all admit atlases, `Z_N[F]` has the leading term at any pair dominating
  every cell, coefficient = Σ over (i,I) of Σ over tied cells of `∫_base β_w · faceCoeff`.

## The remaining gap, as I now see it

To turn a fibre-constant piece (CCXXVIII) into an atlas (CCXXX) one needs, in the normal coordinates
`n` of stratum `I` and tangential `z`:
`|det Dφ_i|·(p∘Φ_i)·(F∘φ_i)·exp(−N K∘φ_i)` on `{|n_j| < ε}` with, on a monomial chart,
`K∘φ_i(z,n) = u(z,n)·(∏_{j∉I, j∈supp e} z_j^{e_j})·∏_{j∈I} n_j^{e_j}` and
`|det Dφ_i| = |v(z,n)|·(∏_{j∉I} |z_j|^{h_j})·∏_{j∈I}|n_j|^{h_j}`.
So even when the chart unit `u` is constant, the EFFECTIVE phase unit on the piece is
`u·∏_{j∉I} z_j^{e_j}` — z-dependent (bounded above and below on the piece since |z_j| ∈ [ε, R]).
And in general `u(z,n)` depends on `n`. The library removes an `n`-dependent unit only by the strip
normalisation (`rescale` one normal coordinate by `unitRoot`), whose region is existential
(`exists_stripNormalisation`, `exists_orthantSplitBoxCharts`), not the prescribed piece.
Also the piece's normal box is two-sided `(−ε,ε)^{|I|}` with `|n_j|^{h_j}` (orthant assembly needed:
the library has `integral_symBox_eq_sum_reflect` for the unit symmetric box and `reflect σ`), and the
phase exponents are `e_j` (hironaka) vs the library's `2k_j` (the paper's even-exponent normal form:
grammar has `even_positive_form_halfExp` for K ≥ 0 giving even exponents via `halfExp`).

## Options for the next unit(s)

(A) Extend the constant-unit cell to a z-DEPENDENT scalar unit `β(z)` continuous, `β_min ≤ β(z) ≤ β_max`:
    kernel at (z,N) = β=1 kernel at time `N β(z)`; pointwise certificate with coefficient
    `β(z)^{−λ}·faceCoeff`; eventual uniform bound via the same `tendstoUniformlyOn_normChart` since
    `N β(z) → ∞` uniformly and the scale ratio `β^{−λ}(1 + log β/log N)^{m−1}` is uniformly bounded.
    Covers the tangential monomial factor when the chart unit is constant. Cheap (1 unit).
(B) Two-sided/orthant assembly: `∫_{(−b,b]^{n+1}} A(z,u)∏|u|^h e^{−βN∏u^{2k}} = ∑_σ (positive-orthant
    kernel with amplitude A(z, reflect σ ·))`, so a two-sided cell is an atlas of 2^{n+1} constant-unit
    cells. Cheap (1 unit).
(C) A PARAMETRISED strip normalisation on a prescribed product piece: for `u(z,n)` analytic, positive on
    a neighbourhood of `base × [−ε,ε]^{r}`, a z-dependent normal rescaling `n_{j₀} ↦ n_{j₀}·u^{1/e_{j₀}}`
    that is a diffeomorphism on the whole piece for ε small enough (uniformly in z on the compact base),
    turning the kernel into constant-unit form on a z-dependent box. Substantive; needs ε small (allowed:
    ε is ours to choose in CCXXIII) and control of the image box (not a product any more — the box side
    depends on z and n?). Please assess feasibility and what exactly the output cell would look like.
(D) Switch programme (your #75 ranking): moment-tensor asymptotics `M_{I,r}(n)` — the kernel with
    monomial insertion `u^α` is `boxKernel` with exponents `h+α` (immediate from CCXXIX), giving the
    Mellin scaling `N^{−λ(h+α)}` of the normal moments and the critical-set shift; then relate to the
    tube fibre measures of CCXX (`condTubeNormalMeasure`) on constant-unit cells.
(E) Coordinate-free face functional: identify `boxFaceCoeff`/`amplitudeCoeff` with the paper's face
    integral `Γ(λ)/(m−1)! a_I ∫_{S_I} (φ∘π)|_{S_I} c_0 |dv|` (eq:thm_leading_coeff) in the tied case
    (all ratios minimal) and show independence of the atlas via uniqueness of the normalised limit
    (`resolvedLeadingCoeff_eq_of_two_adapted_decompositions` from your #75 §5).

Q1. Rank A–E for the next 3–5 units, with reasons (value for the paper's thm:expectation_expansion
    and eq:thm_leading_coeff; honesty; feasibility with the existing library).
Q2. For the top-ranked item, give module contracts (statements, hypotheses, declarations to reuse) in
    the style of #74/#75. If (C) is ranked high, be explicit about the geometry (why a prescribed piece
    can be normalised globally in n for small ε, what the image region is, how the a.e. identity
    `Z N = ∑ cells` is obtained, and whether an exact tiling or an allocation is needed).
Q3. Anything in CCXXVI–CCXXX you consider mis-stated or over-claimed? (Docs call the CCXXX theorem
    "conditional on the adapted geometry".)

## Appendix: exact statements
212:theorem hasLeadingTerm_boltzmannIntegral_of_monomial (e h : ι → Fin d →₀ ℕ)
213-    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
214-    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
215-    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
216-    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
217-    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
218-    (c lam : ι → Finset (Fin d) → ℝ) (k : ι → Finset (Fin d) → ℕ) (lam₀ : ℝ) (k₀ : ℕ)
219-    (hpiece : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
220-      HasLeadingTerm (R.pieceIntegral (fun i => (e i).support) ε i I F K p) (c i I) (lam i I)
221-        (k i I))
222-    (hlam : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty), lam₀ ≤ lam i I)
223-    (hk : ∀ i, ∀ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
224-      lam i I = lam₀ → k i I ≤ k₀) :
225-    HasLeadingTerm (R.boltzmannIntegral F K p)
226-      (∑ i, ∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
227-        (fun I => lam i I = lam₀ ∧ k i I = k₀), c i I) lam₀ k₀ :=
228-  R.hasLeadingTerm_boltzmannIntegral (fun i => (e i).support) ε hFm hF hK hK0 c lam k lam₀ k₀
229-    hpiece hlam hk fun i =>
230-      R.hasLeadingTerm_pieceIntegral_empty_of_monomial i (fun i => (e i).support) ε (hc i) rfl hε
231-        hFm hF hK hK0 lam₀ k₀
232-
233-end ResolutionCover
234-

51:structure AdaptedProductDensity (w : (Fin d → ℝ) → ℝ) (piece : Set (Fin d → ℝ)) where
52-  /-- The tangential base. -/
53-  base : Set (Fin (d - r) → ℝ)
54-  measurableSet_base : MeasurableSet base
55-  /-- The normal box. -/
56-  normalBox : Set (Fin r → ℝ)
57-  measurableSet_normalBox : MeasurableSet normalBox
58-  /-- The tangential weight (measurable only). -/
59-  beta : (Fin (d - r) → ℝ) → ℝ
60-  /-- The normal amplitude. -/
61-  amp : (Fin (d - r) → ℝ) → (Fin r → ℝ) → ℝ
62-  density_ae : (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) => piece.indicator w (planeSplit τ q))
63-    =ᵐ[volume] fun q => base.indicator beta q.1 * normalBox.indicator (amp q.1) q.2
64-
65-theorem measurableEmbedding_planeSplit : MeasurableEmbedding (planeSplit τ) :=
66-  (planeSplit τ).toHomeomorph.measurableEmbedding
67-
218:noncomputable def adaptedProductDensity_of_fibreConstant (β : (Fin d → ℝ) → ℝ)
219-    (hfc : (fun y => (sizePiece (D i) ε I).indicator (R.allocation i) y) =ᵐ[volume]
220-      fun y => (sizePiece (D i) ε I).indicator (fun y => β (planeFoot (stratumSplit I hne) y)) y) :
221-    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
222-      (sizePiece (D i) ε I) where
223-  base := {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I}
224-  measurableSet_base := (measurableSet_footCondition (D i) I).preimage

49:noncomputable def boxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
50-  origPhaseIntegral n h k β N b (fun _ => 0) (A z)
51-
52-/-- **The face coefficient of the box kernel**
53-`b^{Σh+n+1} (b^{2Σk})^{−λ} · amplitudeCoeff h k λ β (A(z, b·))`. -/
54:noncomputable def boxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
55-  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
56-    amplitudeCoeff h k l β fun v => A z (b • v)
57-
58-variable {n h k β b}
59-
60-theorem continuous_amp_of_uncurry (hA : Continuous (Function.uncurry A)) (z : Fin t → ℝ) :
--
65:theorem hasLeadingTerm_boxKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
66-    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
67-    (hA : Continuous (Function.uncurry A)) (z : Fin t → ℝ) :
68-    HasLeadingTerm (boxKernel n h k β b A z) (boxFaceCoeff n h k β b A l z) l
69-      (multCount (ratioExp h k) l - 1) :=
70-  population_box_tendsto n h k hk β hβ hb hmin hatt (A z) (continuous_amp_of_uncurry A hA z)
71-
--
211:theorem eventually_abs_boxKernel_div_le (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
212-    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
213-    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T) :
214-    ∃ C, ∀ᶠ N in atTop, ∀ z ∈ T,
215-      |boxKernel n h k β b A z N / powLogScale l (multCount (ratioExp h k) l - 1) N| ≤ C := by
216-  have hc : 0 < b ^ (2 * ∑ i, k i) := pow_pos hb _
217-  have hK : IsCompact (boxInput n b A hA '' T) := hT.image (continuous_boxInput n b A hA)
--
275:theorem hasLeadingTerm_integral_boxKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
276-    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
277-    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
278-    {βw : (Fin t → ℝ) → ℝ} (hβw : IntegrableOn βw T) :
279-    HasLeadingTerm (fun N => ∫ z in T, βw z * boxKernel n h k β b A z N)
280-      (∫ z in T, βw z * boxFaceCoeff n h k β b A l z) l (multCount (ratioExp h k) l - 1) := by
281-  obtain ⟨C, hC⟩ := eventually_abs_boxKernel_div_le hk hβ hb hl hmin hatt hA hT

47:structure ConstantUnitCell (t : ℕ) where
48-  /-- The normal dimension is `n + 1`. -/
49-  n : ℕ
50-  /-- The density exponents. -/
51-  h : Fin (n + 1) → ℕ
52-  /-- The half phase exponents. -/
53-  k : Fin (n + 1) → ℕ
54-  k_pos : ∀ i, 0 < k i
55-  /-- The constant phase unit. -/
56-  β : ℝ
57-  β_pos : 0 < β
58-  /-- The box side. -/
59-  b : ℝ
60-  b_pos : 0 < b
61-  /-- The amplitude. -/
62-  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
63-  A_cont : Continuous (Function.uncurry A)
64-  /-- The tangential base. -/
65-  base : Set (Fin t → ℝ)
66-  base_compact : IsCompact base
67-  /-- The tangential weight. -/
68-  βw : (Fin t → ℝ) → ℝ
69-  βw_int : IntegrableOn βw base
70-
71-namespace ConstantUnitCell
72-
73-variable {t : ℕ} (c : ConstantUnitCell t)
74-
75-/-- The cell's exponent `λ = min_j (h_j+1)/(2k_j)`. -/
107:structure FiniteConstantUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where
108-  /-- The cell index type. -/
109-  ι : Type
110-  [fintype : Fintype ι]
111-  /-- The cells. -/
112-  cell : ι → ConstantUnitCell t
113-  /-- The exact decomposition. -/
114-  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N
115-
178:theorem hasLeadingTerm_boltzmannIntegral_of_atlases (e h : ι → Fin d →₀ ℕ)
179-    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
180-    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
181-    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
182-    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
183-    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
184-    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
185-      FiniteConstantUnitAtlas d (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
186-    (lam₀ : ℝ) (k₀ : ℕ)
187-    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
188-      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
189-    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
190-      (j : (At i I hI hne).ι),
191-      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
192-    HasLeadingTerm (R.boltzmannIntegral F K p)
193-      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
194-        atlasPieceCoeff At lam₀ k₀ i I) lam₀ k₀ := by
195-  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
196-    (atlasPieceCoeff At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
197-    (fun i I hI => by
198-      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
199-      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
200-      unfold atlasPieceCoeff

231:theorem exists_stripNormalisation {i : Fin d} {V : Set (Fin d → ℝ)} (hV : IsOpen V)
232-    {ρ : (Fin d → ℝ) → ℝ} (hρ : AnalyticOnNhd ℝ ρ V) (hρpos : ∀ y ∈ V, 0 < ρ y)
233-    {Q₀ : Set (Fin d → ℝ)} (hQ₀ : IsCompact Q₀) (hQ₀V : Q₀ ⊆ V) (hQ₀i : ∀ y ∈ Q₀, y i = 0) :
234-    ∃ (b₀ b : ℝ) (S : Set (Fin d → ℝ)), 0 < b₀ ∧ 0 < b ∧ IsOpen S ∧ S ⊆ V ∧
235-      cylinder i Q₀ (b₀ / 2) ⊆ S ∧ InjOn (rescale i ρ) S ∧
236-      (∀ y ∈ S, 0 < ρ y + y i * fderiv ℝ ρ y (Pi.single i 1)) ∧
237-      IsOpen (rescale i ρ '' S) ∧ cylinder i Q₀ b ⊆ rescale i ρ '' S ∧
238-      ∀ z ∈ rescale i ρ '' S, AnalyticAt ℝ (Function.invFunOn (rescale i ρ) S) z := by
239-  classical
240-  rcases Q₀.eq_empty_or_nonempty with hemp | hne
241-  · subst hemp
37:theorem integral_symBox_eq_sum_reflect :
38-    ∀ (d : ℕ) (F : (Fin d → ℝ) → ℝ), Continuous F →
39-      ∫ x in symBox d, F x = ∑ σ : Fin d → Bool, ∫ u in unitBox d, F (reflect σ u) := by
40-  intro d
160:theorem tendstoUniformlyOn_normChart (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
161-    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
162-    (K : Set (InputSpace (d + 1))) (hK : IsCompact K) :
163-    TendstoUniformlyOn (fun N x => normChart h k l β N x) (limChart h k l β) atTop K := by
