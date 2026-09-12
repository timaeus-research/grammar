# Consult #94 — after #93 A–D: audit, and what remains worth doing

Context: Lean 4 formalisation of the grammar paper (Gerraty–Murfet), repo `timaeus-research/grammar`, 611 modules,
axiom-clean. Consult #93 audited the coordinate-free expansion theorem (CCCIII) and ordered the remaining work
A (first instance) → D (uniqueness) → B (jets ↔ series) → C (leading measure) → E (projector blow-up). A–D are done;
your "small completion tasks" are done. This consult: (1) audit what landed; (2) decide what, if anything, remains
worth doing on the coordinate-free programme; (3) the honest paper-facing summary.

## Landed since #93 (Lean excerpts)

### CCCIV `CoordFreeExpansionCompletion`
42:theorem summable_field_pair (I : Finset R.Component) (q : PowerLogIndex) (s : R.Stratum I) :
43-    Summable fun r : ℕ =>
44-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r) := by
45-  have hterm : ∀ r : ℕ, (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)
46-      = ∑ J, if hJ : C.strat J = I then C.weight hJ s * ((r.factorial : ℝ)⁻¹ *
66:theorem integrable_tsum_field_pair (I : Finset R.Component) (q : PowerLogIndex) :
67-    Integrable (fun s : R.Stratum I => ∑' r : ℕ,
68-      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r))
69-      (C.stratumMeasure I) := by
70-  have heq : (fun s : R.Stratum I => ∑' r : ℕ,
86:noncomputable def spectrumLe (Q Dg : ℕ) (A : ℝ) : Finset PowerLogIndex :=
87-  (spectrumBelow Q Dg A).filter fun q => q.exponent ≤ A
88-
89-/-- A power–log term with exponent `α > A` is `o(n^{−A})`, whatever its log degree. -/
90:theorem isLittleO_scale_of_lt {A α : ℝ} (hα : A < α) (j : ℕ) :
91-    (fun n : ℝ => n ^ (-α) * Real.log n ^ j) =o[atTop] fun n : ℝ => n ^ (-A) := by
92-  have hlog : (fun n : ℝ => Real.log n ^ j) =o[atTop] fun n : ℝ => n ^ (α - A) := by
93-    have h := isLittleO_log_rpow_rpow_atTop (j : ℝ) (sub_pos.2 hα)
94-    refine h.congr_left fun n => ?_
112:theorem hasCoordFreeExpansion_le (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
113-    (hφ : Measurable φ) :
114-    D.HasCoordFreeExpansion C.stratumMeasure Cc.field
115-      (spectrumLe (commonQ C.adapted.k) (commonD C.n)) W K ϕ φ := by
116-  intro Ac
Docstrings corrected per #93 (spec = indexing envelope; `cc` = factorisation family; fields chosen; unnormalised integral);
`ResolvedNormalData` gained `finiteDimensional_N`.

### CCCV–CCCVII: the first instance `∫_0^ρ P(x) e^{−nx²} dx` (half-interval, ONE chart)
46:noncomputable def geometry : ResolvedGeometry 1 Space where
47-  π := id
48-  continuous_π := continuous_id
49-  proper_π := isProperMap_id
50-  Component := Unit
51-  E := fun _ => {u : Space | u 0 = 0}
52-  isClosed_E := fun _ => isClosed_eq (continuous_apply 0) continuous_const
53-  k := fun _ => 1
54-  h := fun _ => 0
55-  k_pos := fun _ => one_pos
56-
142:noncomputable def normalData : ResolvedNormalData geometry ℝ where
143-  N := fun I _ => normalSpace I
144-  finrank_N := fun I _ => finrank_normalSpace I
145-  finiteDimensional_N := fun I _ => inferInstance
146-  du := fun I _ _ => (normalSpace I).subtype
147-  du_linearIndependent := fun I _ => linearIndependent_subtype I
148-  Φ := fun _ s v => fun _ => s.1 0 + (v : ℝ)
149-  Φ_zero := fun _ s => by
150-    funext i
151-    rw [Fin.fin_one_eq_zero i]
75:noncomputable def polySeries : FormalMultilinearSeries ℝ Space ℝ :=
76-  fun m => f (fun _ => m) • monomialForm (fun _ : Fin m => (0 : Fin 1))
77-
--
102:theorem hasFPowerSeriesOnBall_poly : HasFPowerSeriesOnBall (poly f) (polySeries f) 0 ⊤ where
103-  r_le := by rw [radius_polySeries f hf]
104-  r_pos := ENNReal.zero_lt_top
--
145:theorem jetFamily_poly : jetFamily 0 (poly f) = f := by
146-  funext bb
147-  obtain ⟨m, rfl⟩ : ∃ m, bb = fun _ => m := ⟨bb 0, funext fun i => by rw [Fin.fin_one_eq_zero i]⟩
181:noncomputable def chart :
182-    ChartPresentation (locData f hf ρ b hb) ((partition f hf ρ b hb).ρ 0) Base 0 1 where
183-  ν := Measure.dirac basePt
184-  isFiniteMeasure_ν := inferInstance
185-  h := fun _ => 0
186-  k := fun _ => 1
187-  k_pos := fun _ => one_pos
188-  b := b
189-  b_pos := hb
190-  Φ := Prod.snd
191-  measurable_Φ := measurable_snd
192-  c := fun _ => 1
193-  measurable_c := measurable_const
194-  nonneg_c := Eventually.of_forall fun _ => zero_le_one
195-  x := ContinuousMap.const Base (datum f hf b hb)
196-  transport := transport_chart f hf ρ b hb hbρ
197-  phase_normal := Eventually.of_forall fun p => by
198-    change p.2 0 ^ 2 = 1 * ∏ i : Fin 1, p.2 i ^ (2 * 1)
199-    rw [Fin.prod_univ_one, one_mul, mul_one]
200-  amplitude_eq := Eventually.of_forall fun p => by
201-    rw [ContinuousMap.const_apply, toEta_datum]
225:noncomputable def certificate :
226-    ResolvedCertificate geometry normalData (region ρ) phase (fun _ => (1 : ℝ)) (poly f) where
227-  L := locData f hf ρ b hb
228-  obs_eq := rfl
229-  phase_eq := rfl
230-  transport := by
231-    change Measure.map id (volume.restrict (region ρ)) = _
232-    rw [Measure.map_id]
233-    have : (fun _ : Space => ENNReal.ofReal (1 : ℝ)) = 1 := by
234-      funext _
235-      simp
236-    rw [this, withDensity_one]
237-  M := 1
238-  n := fun _ => 0
239-  strat := fun _ => Finset.univ
240-  base := fun _ => Set.univ
241-  isCompact_base := fun _ => isCompact_univ
242-  β := 1
243-  β_pos := one_pos
244-  adapted := ⟨partition f hf ρ b hb, fun _ => chart f hf ρ b hb hbρ⟩
245-  T := fun _ => presentation f hf ρ b hb hbρ
246-  frame := fun _ _ => frameUniv
247-  Φ_eq := fun _ s u => by
254:noncomputable def coeffCertificate : (certificate f hf ρ b hb hbρ).CoefficientCertificate where
255-  cc := fun _ _ => deltaFamily 1
256-  cc_abs := fun _ _ => absSummableAt_deltaFamily 1 b
257-  jet_abs := fun _ s => by
258-    change AbsSummableAt (jetFamily 0 (poly f)) b
259-    rw [jetFamily_poly f hf]
260-    exact absSummableAt_of_support f hf b
261-  datum_eq := fun _ s => by
262-    change toEta b (datum f hf b hb) = CoeffFamily.conv (deltaFamily 1) (jetFamily 0 (poly f))
263-    rw [toEta_datum, jetFamily_poly f hf, conv_deltaFamily]
275:theorem hasCoordFreeExpansion_poly :
276-    normalData.HasCoordFreeExpansion (certificate f hf ρ b hb hbρ).stratumMeasure
277-      (coeffCertificate f hf ρ b hb hbρ).field (spectrumLe 2 0) (region ρ) phase
278-      (fun _ => (1 : ℝ)) (poly f) := by
279-  have h := (coeffCertificate f hf ρ b hb hbρ).hasCoordFreeExpansion_le measurable_phase
280-    measurable_const (fun _ => zero_le_one) (continuous_poly f hf).measurable
281-  rwa [commonQ_certificate, commonD_certificate] at h
282-
283-/-- The original integral in this instance is `∫_{[0,ρ]} P(w) e^{−n w²} dw`. -/
(The half-interval `W = [0,ρ]` was chosen so that ONE chart (box `(0,b]`, `Φ(s,u) = u`) suffices; a two-sided interval
needs a second chart with `Φ(s,u) = −u`. The transport identity is Lebesgue on `(0,b]` vs `[0,ρ] ∩ {x² < b²}` up to the
null set `{0, b}`.)

### CCCVIII `CutoffExpansionUniqueness`
72:theorem CutoffExpansion.coeff_eq_zero_of_zero {Q D : ℕ} (hQ : 0 < Q) {c : ℝ → ℕ → ℝ}
73-    (h : CutoffExpansion Q D (fun _ => 0) c) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ}
74-    (hj : j ≤ D) : c μ j = 0 := by
75-  by_contra hne
76-  have hmem : (μ, j) ∈ indexSet D Q (μ + 1) := by
77-    unfold indexSet
78-    obtain ⟨m, rfl⟩ := hμ
79-    exact Finset.mem_product.2 ⟨mem_latticeBelow hQ (by linarith), Finset.mem_range.2
91:theorem CutoffExpansion.coeff_unique {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c c' : ℝ → ℕ → ℝ}
92-    (h : CutoffExpansion Q D Z c) (h' : CutoffExpansion Q D Z c') {μ : ℝ}
93-    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) : c μ j = c' μ j := by
94-  have hsub := h.sub h'
95-  have hz : (fun N => Z N - Z N) = fun _ => (0 : ℝ) := funext fun N => sub_self _
96-  rw [hz] at hsub
97-  exact sub_eq_zero.1 (CutoffExpansion.coeff_eq_zero_of_zero hQ hsub hμ hj)
98-
126:theorem CutoffExpansion.coeff_eq_of_lattices {Q Q' D D' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q')
127-    {Z : ℝ → ℝ} {c c' : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) (h' : CutoffExpansion Q' D' Z c')
128-    (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (hcD : ∀ μ j, D < j → c μ j = 0)
129-    (hc' : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q') → ∀ j, c' μ j = 0)
130-    (hcD' : ∀ μ j, D' < j → c' μ j = 0) (μ : ℝ) (j : ℕ) : c μ j = c' μ j := by
131-  by_cases hj : j ≤ max D D'
132-  · by_cases hμ : (∃ m : ℕ, μ = (m : ℝ) / Q) ∨ ∃ m : ℕ, μ = (m : ℝ) / Q'
133-    · exact CutoffExpansion.coeff_unique_of_lattices hQ hQ' h h' hc hcD hc' hcD' hμ hj
182:theorem ResolvedCertificate.CoefficientCertificate.expansionCoefficient_eq_of_certificates
183-    {C C' : ResolvedCertificate R D W K ϕ φ} (Cc : C.CoefficientCertificate)
184-    (Cc' : C'.CoefficientCertificate) (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
185-    (hφ : Measurable φ) (q : PowerLogIndex) :
186-    D.expansionCoefficient C.stratumMeasure Cc.field φ q =
187-      D.expansionCoefficient C'.stratumMeasure Cc'.field φ q := by
188-  rw [Cc.expansionCoefficient_eq_gCoeff, Cc'.expansionCoefficient_eq_gCoeff]
189-  exact CutoffExpansion.coeff_eq_of_lattices (commonQ_pos C.adapted.k C.adapted.k_pos)

### CCCIX `JetFamilyOfSeries`
68:theorem weightComponent_normalJet_eq {F : (Fin d → ℝ) → ℝ}
69-    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F p 0 R)
70-    {r : ℕ} (bb : Fin d → ℕ) (hb : ∑ i, bb i = r) :
71-    weightComponent (normalJet F r) bb =
72-      (Nat.multinomial Finset.univ bb : ℝ)⁻¹ * ((r.factorial : ℝ) * monoCoeff p r bb) := by
73-  rw [weightComponent_def, card_weightFibre bb hb]
74-  congr 1
90:theorem jetFamily_eq_monoFamily {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
91-    {p : FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
92-    (hF : HasFPowerSeriesOnBall F p 0 R) : jetFamily n F = monoFamily p := by
93-  funext bb
94-  rw [jetFamily_eq n F rfl, weightComponent_normalJet_eq hF bb rfl]
95-  unfold monoFamily
96-  have hm := multinomial_div_factorial bb rfl
104:theorem absSummableAt_jetFamily {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
105-    {p : FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
106-    (hF : HasFPowerSeriesOnBall F p 0 R) {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) {b : ℝ} (hb : 0 ≤ b)
107-    (hbρ : ((n + 1 : ℕ) : ℝ) * b < ρ) : AbsSummableAt (jetFamily n F) b := by
108-  rw [jetFamily_eq_monoFamily hF]
109-  exact absSummableAt_monoFamily p (hρ.trans_le hF.r_le) hb hbρ
110-
122:noncomputable def ResolvedCertificate.CoefficientCertificate.ofSeries
123-    (cc : ∀ J, ↥(C.base J) → CoeffFamily (C.n J + 1))
124-    (cc_abs : ∀ J s, AbsSummableAt (cc J s) (C.adapted.b J))
125-    (ρ : ∀ J, ↥(C.base J) → ℝ≥0) (hρ : ∀ J s, ((ρ J s : ℝ≥0) : ℝ≥0∞) < (C.T J).R s)
126-    (hbρ : ∀ J s, ((C.n J + 1 : ℕ) : ℝ) * C.adapted.b J < ρ J s)
127-    (datum_eq : ∀ J s, toEta (C.adapted.b J) ((C.adapted.chart J).x s) =
128-      CoeffFamily.conv (cc J s) (monoFamily ((C.T J).p s))) :

### CCCX `CoordFreeLeadingTerm`
60:def PowerLogIndex.Precedes (q' q : PowerLogIndex) : Prop :=
61-  precedes (q'.exponent, q'.logDegree) (q.exponent, q.logDegree)
62-
63-namespace ResolvedCertificate
64-
65-variable (C : ResolvedCertificate R D W K ϕ φ)
66-
67-/-- The admissible power–log indices of a certificate: exponents in `commonQ⁻¹ℕ`, log degrees
68-`≤ commonD`. -/
69:def AdmissibleIndex (q : PowerLogIndex) : Prop :=
70-  (∃ m : ℕ, q.exponent = (m : ℝ) / commonQ C.adapted.k) ∧ q.logDegree ≤ commonD C.n
71-
72-namespace CoefficientCertificate
73-
74-variable {C} (Cc : C.CoefficientCertificate)
75-
76-/-- ★★ **The leading term of the coordinate-free expansion**: at an admissible index all of whose
77-predecessors carry zero coordinate-free coefficient,
78-`∫_W φ ϕ e^{−nK} / (n^{−λ}(log n)^j) →
80:theorem hasLeadingTerm_expansionCoefficient (hK : Measurable K) (hϕ : Measurable ϕ)
81-    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ) (q : PowerLogIndex) (hq : C.AdmissibleIndex q)
82-    (hfirst : ∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
83-      D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0) :
84-    HasLeadingTerm (globalLaplace W K fun w => φ w * ϕ w)
85-      (D.expansionCoefficient C.stratumMeasure Cc.field φ q) q.exponent q.logDegree := by
86-  rw [Cc.expansionCoefficient_eq_gCoeff]
87-  refine CutoffExpansion.hasLeadingTerm_of_first (commonQ_pos _ C.adapted.k_pos)
88-    (C.cutoffExpansion_globalLaplace hK hϕ hϕ0 hφ) hq.1 hq.2 fun p hp hpre => ?_
89-  have := hfirst ⟨p.1, p.2⟩ ⟨hp.1, hp.2⟩ hpre
103:theorem exists_first_nonzero_expansionCoefficient (hK : Measurable K) (hϕ : Measurable ϕ)
104-    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ)
105-    (hne : ∃ q : PowerLogIndex, C.AdmissibleIndex q ∧
106-      D.expansionCoefficient C.stratumMeasure Cc.field φ q ≠ 0) :
107-    ∃ q : PowerLogIndex, C.AdmissibleIndex q ∧
108-      D.expansionCoefficient C.stratumMeasure Cc.field φ q ≠ 0 ∧
109-      (∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
110-        D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0) ∧
111-      (globalLaplace W K fun w => φ w * ϕ w) ~[atTop] fun N =>
112-        D.expansionCoefficient C.stratumMeasure Cc.field φ q *
141:theorem expansionCoefficient_eq_integral_leadingMeasure (hK : Measurable K) (hϕ : Measurable ϕ)
142-    (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ) (q : PowerLogIndex) (hq : C.AdmissibleIndex q)
143-    (hfirst : ∀ q' : PowerLogIndex, C.AdmissibleIndex q' → q'.Precedes q →
144-      D.expansionCoefficient C.stratumMeasure Cc.field φ q' = 0)
145-    {σ : Measure (Fin d → ℝ)} (hσ : HasLeadingMeasure W K q.exponent q.logDegree σ)
146-    (a : (Fin d → ℝ) →ᵇ ℝ) (ha : ∀ w, a w = φ w * ϕ w) :
147-    D.expansionCoefficient C.stratumMeasure Cc.field φ q = ∫ w, a w ∂σ := by
148-  have h1 := Cc.hasLeadingTerm_expansionCoefficient hK hϕ hϕ0 hφ q hq hfirst
149-  have h2 := hσ a
150-  have heq : globalLaplace W K a = globalLaplace W K fun w => φ w * ϕ w := by

All `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The paper mirror paragraph now records: the representation
theorem, the truncation, canonicity of the assembled scalar coefficients, the leading term and the leading-measure bridge,
jets = series, the hand-built one-dimensional instance, and the non-claims (fields chosen; factorisation family; no instance
from the hironaka interface; unnormalised integral).

## Questions

1. **Audit** the five units for correctness of statement and honesty of phrasing. In particular: (a) is
   `expansionCoefficient_eq_of_certificates` the right canonicity statement (it quantifies over two certificate pairs for the
   SAME `(W, K, ϕ, φ)`; the observable is fixed)? (b) is the leading-measure bridge correctly scoped (it needs `φϕ` to be
   represented by a bounded continuous test and `W` to have a leading measure in the CCXC sense)? (c) anything misleading in
   "the theorem is inhabited" given that the instance is one-dimensional with a single chart and the zero at the boundary
   of `W`? (d) `AdmissibleIndex` uses the certificate's lattice — fine as the hypothesis of the leading-term theorem?
2. **What remains worth doing?** Candidates: (E) the projector blow-up model of the isolated zero `|x|²` in dimension `d`
   as a `ResolvedGeometry` with certificates (large; the CCXCV/CCLXXXIV `BlowUpCube` machinery exists on the
   `ResolutionCover`/`ProductMonomialChartVar` side, not on the `AdaptedStrataData` side); (F) a two-variable tied-crossing
   instance `∫_{[0,b]²} P(x,y) e^{−n x² y²}` on the square small enough that the sublevel set covers it (one chart at the
   tied stratum `S_{12} = {0}` with normal space `ℝ²`, `k = (1,1)`, `Q = 2`, `D = 1`: log terms and the infinite-normal-order
   phenomenon); (G) the two-sided interval (second chart with `Φ = −u`); (H) closed-form values of the 1D coefficients from
   `monoKernel` (`√π/2 n^{−1/2} + a√π/4 n^{−3/2}` for `P = 1 + ax²`) — a regression test of the whole pipeline against the
   known Gaussian moments; (I) a `ResolvedCoreCertificate` on `AnalyticCoreDecomposition` (cores + phase-gap tail) instead of
   `AdaptedStrataData` (sublevel partition), which is what general phases with curved sublevel sets need; (J) an
   observable-independent version: freeze geometry/density data and quantify over a class of observables, so that
   `φ ↦ expansionCoefficient` is a functional; (K) stop here. Rank; say which are gates for any further headline and which
   are bookkeeping; estimate sizes.
3. **Paper-facing summary** (≤ 10 lines, for the user): what is now proved about the asymptotic expansion of the partition
   function with insertion in coordinate-free terms, what is conditional on what, and what is not proved.

Answer in sections 1–3, tersely.
