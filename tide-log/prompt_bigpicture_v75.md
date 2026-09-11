# Consult #75 — grammar Lean: discharging the per chart–stratum leading-term certificates

You are advising on the Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper
(library `Grammar`, 526 modules, axiom-clean). Your consult #74 designed a chart-local
resolved-space programme (7 modules). ALL SEVEN ARE NOW LANDED. This consult asks how to close the
remaining gap between the exact chart–stratum decomposition and the identified exponent pair, and
what programme should follow.

## What is landed (exact Lean statements below)

* CCXX weights in the fibre chain: `TubeWeight d` = bounded nonneg measurable `w : (Fin d → ℝ) → ℝ`;
  all fibre theorems are `∫ y in U', wt.w y * F y = ∫ y in U', wt.w y * condContractionSeries … F (proj y)`
  with the weight carried by the fibre measures (`tubeDensity T C wt`).
* CCXXI/CCXXII coordinate planes `P_I` as analytic LCI strata with strucdual's tube of every radius,
  Jacobian 1, `planeSplit : ℝ^{d−r} × ℝ^r ≃L ℝ^d`.
* CCXXIII coordinate-size tiling of a chart: `sizePiece D ε I = {y | ∀ j ∈ D, (|y j| < ε ↔ j ∈ I)}`
  (measurable, disjoint, exhaustive), each nonempty piece inside the ε-tube of `P_I` and
  fibre-saturated; per chart–stratum formula `integral_sizePiece_eq_integral_condContraction`.
* CCXXIV `ResolvedChartExpansion`: chart weight
  `chartWeight R i c : TubeWeight d`, `w y = 1_{dom_i}(y) · |det Dφ_i y| · ρ_i(Φ_i y) · c(Φ_i y)`
  (ρ_i = normalised indicator cover weight `coverWeight` — MEASURABLE ONLY, ≤ 1, sums to 1 on the
  union of images; c = `TubeWeight.boltzmann N K p` = `e^{−N K} p`); exact
  `coverIntegral_eq_sum_chartWeight`, `coverIntegral_eq_sum_chart_pieces`,
  `coverIntegral_eq_sum_pieceContraction`.
* CCXXV `LeadingTermInterface`: `HasLeadingTerm Z c λ k := Tendsto (fun N => Z N / (N^(−λ) * log N ^ k)) atTop (𝓝 c)`;
  bridge to `IsEquivalent` both ways; `PairDominates`; `HasLeadingTerm.of_dominated`;
  `hasLeadingTerm_sum_extremal` (finite sums, ties summed, cancellation allowed);
  `boltzmannIntegral_eq_sum_pieces` (CCXXIV for every N ≥ 0);
  `hasLeadingTerm_boltzmannIntegral` (leading term of Z_N[F] from per-piece certificates + vanishing
  of the divisor-free pieces at the extremal scale).

Existing single-chart asymptotics (unconditional, on hironaka's chart form):
* `IsMonomialChart K φ dom e h W` (hironaka): W open ⊇ dom, φ analytic on W, injOn where `y^h ≠ 0`,
  continuous nonvanishing units u, v with `K ∘ φ = u · y^e`, `det Dφ = v · y^h` (grammar upgrades
  u, v to analytic: `exists_analytic_unit`, `exists_analytic_jacUnit`).
* CCV `IsMonomialChart.local_leading_term`: for y₀ ∈ W with K(φ y₀) = 0, F analytic near φ y₀ with
  F(φ y₀) > 0, K ≥ 0 analytic near φ y₀: ∃ centred chart data C and a compact region Ω ∋ φ y₀ inside
  φ(W) with `(fun N => ∫ x in Ω, F x * exp(−N K x)) ~[atTop] fun N => c * (N^(−C.lam) * log N^(C.mult−1))`,
  c = `localLeadingCoeff` > 0, `C.lam = min_j (h_{n_j}+1)/(2k_j)`, `C.mult` = #minimisers. The region Ω
  is EXISTENTIAL (a `localRegion` = image of a tangential compact base × small normal box under φ,
  split into orthants), not a prescribed set.
* CCVIII `exponent_of_analytic`: Θ(N^{−λ*} log^{m*−1}) for ∫ over some compact nbhd of a zero, λ*,m*
  = extremal pair over divisor points of the charts; CCIX identifies it with the small-ball pair.
* `GlobalExponentBound`: `regionIntegral_le_sum` etc. — Θ-bounds by sandwiching between pieces, with
  tails `e^{−Nδ}`.

## The gap

`hasLeadingTerm_boltzmannIntegral` needs, for every chart i and nonempty I ⊆ D_i,
  `HasLeadingTerm (fun N => ∫ y in sizePiece (D i) ε I, 1_{dom_i} |det Dφ_i| ρ_i(φ_i y) e^{−N K(φ_i y)} p(φ_i y) F(φ_i y) dy) (c i I) (lam i I) (k i I)`
plus `HasLeadingTerm (piece ∅) 0 lam₀ k₀` and an extremal pair (lam₀, k₀).

Obstacles as I see them:
1. ρ_i ∘ φ_i is a normalised indicator ratio — not analytic, not even continuous. Every existing
   leading-term theorem needs an analytic amplitude.
2. The region `sizePiece ∩ dom_i` is a coordinate-size region intersected with an ARBITRARY compact
   dom_i, whereas CCV produces its own region Ω (existential).
3. On `sizePiece … I` the divisor coordinates in I are < ε but there is no lower bound; the
   coordinates in D∖I are ≥ ε, so on the piece the phase `u y^e` has the factors j ∈ I small — the
   stratum S_I is the relevant one; the piece's tangential base is `dom_i ∩ {…≥ ε}` in the other
   coordinates, again arbitrary.
4. The divisor-free piece: on `sizePiece D ε ∅ ∩ dom_i`, `y^e ≥ ε^{|e|}` and u ≥ u_min > 0 (compact),
   so `K∘φ_i ≥ δ` and the term is `O(e^{−Nδ})` — this seems straightforward (`Localisation.lean`
   has `localisation_bound`).

## Questions

Q1. What is the honest theorem to aim for? Options I see:
  (A) Θ-only: prove `Z_N[F] = Θ(N^{−λ*} log^{m*−1})` for F > 0 over the union of the chart images
      by sandwiching (lower bound: one CCV region inside one piece; upper bound: sum of pieces each
      bounded by a CCV-type upper bound) — essentially CCVIII for the resolved integral. Does this
      add anything beyond CCVIII/CCIX?
  (B) Exact certificates per piece with ρ_i: replace the cover weights by a measurable partition
      (indicators of a.e.-disjoint sets `A_i ⊆ image_i`) — still non-analytic amplitudes; is there a
      route via monotone approximation (F ρ sandwiched between analytic amplitudes) that yields a
      LIMIT for the ratio, or does the coefficient genuinely depend on ρ (so per-piece certificates
      exist but are not canonical)?
  (C) Restrict the theorem class: assume a resolution cover whose chart images are a.e. disjoint
      (`ρ_i = 1` a.e. on image_i) — is this obtainable from hironaka's `PartialResolution` (the
      `inj` off E gives injectivity per chart but not disjointness across charts)? If not, is a
      disjointification of the images (measurable) compatible with anything analytic?
  (D) Certificates for the piece integrals via the fibre formula: on the piece, the weight
      `w = 1_dom ρ |v| y^h e^{−N u y^e} p` lives in the fibre measure and the observable is
      `F ∘ φ_i` (analytic) — could the moments `∫ n^α dκ_z(n)` of the fibre measures (normal
      coordinates I, phase `u(z,n) n^{e_I}`, weight `|v| n^{h_I} · 1_{dom} ρ`) be certified to
      have leading terms via the Mellin machinery already in the library (`MellinMoment`,
      `CoeffFamily`, `dataBoxCoeff_population_leading_b`) fibrewise, so that the certificate is
      obtained by integrating over the base z ∈ S_I with dominated convergence? What exactly is
      needed of `1_dom ρ` for this (measurable and bounded may suffice if the Mellin asymptotics are
      uniform in the tangential variable and only the leading coefficient depends on the weight
      through a base integral)?
  Rank these; identify which is (i) provable with the existing library in a few units, (ii) closest
  to the paper's theorem (thm:expectation_expansion), (iii) honest about non-claims.

Q2. For the route you rank first, specify precise module contracts (statements, hypotheses, which
  existing declarations to reuse), in the style of your #74 answer. Be careful about: the arbitrary
  compact dom_i; the non-analytic ρ_i; ties/cancellation across (i, I); signed F; the role of ε.

Q3. If the chosen route only yields Θ or an inequality for the coefficient, say so, and say what
  extra hypothesis (e.g. analytic partition of unity as a HYPOTHESIS, or a.e.-disjoint images)
  would upgrade it to an exact coefficient — so it can be recorded as a conditional theorem.

Q4. After this gap: what is the next most valuable programme for the paper? Candidates: (iv) the
  statistical transfer of the identified pair to the empirical/posterior objects of §4 (the
  fluctuation function, log-generating function — already formalised at the population level);
  the coordinate-free leading coefficient formula (eq:thm_leading_coeff) with the face functional
  identified; or the moment-tensor asymptotics `M_{I,r}(n)` (eq:moment_tensor_defn) with explicit
  Mellin scaling per stratum. Rank briefly.

Answer in Lean-aware mathematical prose with proposed declaration names; do not claim upstream
Mathlib names you are not sure of.

## Addendum (after CCXXVI, before the consult could run)

* Obstacle 4 is closed: `Grammar/DivisorFreePieces.lean` proves `hasLeadingTerm_pieceIntegral_empty_of_monomial`
  (phase bounded below on the divisor-free piece of a monomial chart's compact domain) and
  `hasLeadingTerm_boltzmannIntegral_of_monomial` (interface with `D_i = supp e_i`; certificates
  needed only for the NONEMPTY chart–stratum pieces).
* Option (A) seems to add nothing: CCVIII already gives Θ over the compact set resolved by the
  `PartialResolution`, which is a.e. the union of the chart images. Please confirm or correct.
* My diagnosis of the real obstruction, for you to check: the paper's Lemma adapted_pou makes the
  partition weights CONSTANT ON NORMAL FIBRES so they factor out of the normal expansion; the
  measurable cover weights `ρ_i ∘ φ_i` and the indicator of an arbitrary compact `dom_i` are not
  fibre-constant, so the per-piece leading coefficient genuinely depends on them through the trace of
  the piece on the stratum (the face integral), and only a fibre-saturated product piece with a
  fibre-constant weight has a canonical coefficient. CCXXIII shows `sizePiece` IS fibre-saturated on
  the ε-tube of `P_I`; the obstruction is entirely in `1_{dom_i} · ρ_i∘φ_i`. A conditional theorem
  with the hypothesis "the pulled-back weight is fibre-constant on the piece" (the paper's own
  hypothesis) may be the honest exact-coefficient statement. Please assess, and say whether hironaka's
  `PartialResolution` (chart domains: are they boxes/polydiscs?) can be upgraded to fibre-saturated
  domains and fibre-constant weights by shrinking/tiling.
* CCV's region is local in the tangential direction too (`A' = A ∩ closedBall 0 B`, `B` existential,
  from the strip normalisation of the phase unit); a whole-stratum piece therefore needs a finite
  tangential cover with additivity of the face coefficients — the exact-tiling machinery of
  CXCIV (`AnalyticCoreDecomposition`, `gCoeff`, `first_nonzero`) is the existing tool. Please say
  whether that is the route (D') you would take, and what its module contracts are.

## Appendix: exact statements (from the repository)
225:theorem integral_sizePiece_eq_integral_condContraction {F : (Fin d → ℝ) → ℝ}
226-    (hF : IntegrableOn (fun y => wt.w y * F y) (sizePiece D ε I))
227-    {q : (Fin (d - (I.card - 1 + 1)) → ℝ) → FormalMultilinearSeries ℝ (Fin (I.card - 1 + 1) → ℝ) ℝ}
228-    {Rad : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ≥0∞}
229-    (hq : ∀ z, HasFPowerSeriesOnBall (fun n => F (planeSplit (stratumSplit I hne) (z, n))) (q z) 0
230-      (Rad z))
231-    (hη : ∀ z, ∀ᵐ n ∂fibreMeasure volume (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
232-      wt)
233-      z, n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad z))
234-    (hdom : ∀ z, Summable fun k => ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
235-      (tubeDensity (stratumTube hε I hne) (stratumChart I hne) wt) z) :
236-    ∫ y in sizePiece D ε I, wt.w y * F y =
237-      ∫ y in sizePiece D ε I, wt.w y * condContractionSeries (stratumTube hε I hne)
238-        (stratumChart I hne) wt F (planeFoot (stratumSplit I hne) y) := by
239-  have hmeas := measurableSet_sizePiece D ε I

108:noncomputable def chartWeight : TubeWeight d where
109-  w := (R.chart i).dom.indicator fun y =>
110-    (R.chart i).jac y * (R.weight i ((R.chart i).Φ y) * c.w ((R.chart i).Φ y))
111-  measurable := ((R.chart i).measurable_jac.mul
293:theorem coverIntegral_eq_sum_pieceContraction (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε)
294-    {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
295-    (hint : Integrable (fun x => F x * p.w x * Real.exp (-N * K x))
296-      (volume.restrict (⋃ i, R.image i)))
297-    (q : ι → ∀ I : Finset (Fin d), I.Nonempty →
298-      (Fin (d - (I.card - 1 + 1)) → ℝ) → FormalMultilinearSeries ℝ (Fin (I.card - 1 + 1) → ℝ) ℝ)
299-    (Rad : ι → ∀ I : Finset (Fin d), I.Nonempty → (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ≥0∞)
300-    (hq : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, HasFPowerSeriesOnBall
301-      (fun n => F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) (q i I hne z) 0
302-      (Rad i I hne z))
303-    (hη : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, ∀ᵐ n ∂fibreMeasure volume
304-      (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
305-        (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z,
306-      n ∈ Metric.eball (0 : Fin (I.card - 1 + 1) → ℝ) (Rad i I hne z))
307-    (hdom : ∀ i I (hne : I.Nonempty), I ⊆ D i → ∀ z, Summable fun k =>
308-      ‖q i I hne z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
309-        (tubeDensity (stratumTube hε I hne) (stratumChart I hne)
310-          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))) z) :
311-    R.coverIntegral (fun x => F x * p.w x) (fun x => -N * K x) =
312-      ∑ i, ((∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
313-          ∫ y in sizePiece (D i) ε I,
314-            (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y *
315-              pieceContraction hε (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p))
316-                (fun y => F ((R.chart i).φ y)) I y) +
317-        ∫ y in sizePiece (D i) ε ∅,
318-          (R.chartWeight i (TubeWeight.boltzmann N hN K hK hK0 p)).w y * F ((R.chart i).φ y)) := by
319-  rw [R.coverIntegral_eq_sum_chart_pieces N hN K hK hK0 p D ε hFm hint]
320-  refine Finset.sum_congr rfl fun i _ => ?_
321-  congr 1
322-  refine Finset.sum_congr rfl fun I hI => ?_
323-  obtain ⟨hIpow, hne⟩ := Finset.mem_filter.1 hI

49:def HasLeadingTerm (Z : ℝ → ℝ) (c lam : ℝ) (k : ℕ) : Prop :=
50-  Tendsto (fun N => Z N / powLogScale lam k N) atTop (𝓝 c)
51-
52-variable {Z Z' : ℝ → ℝ} {c c' lam lam' : ℝ} {k k' : ℕ}
53-
54-theorem HasLeadingTerm.congr' (h : HasLeadingTerm Z c lam k) (hZ : Z =ᶠ[atTop] Z') :
55-    HasLeadingTerm Z' c lam k :=
56-  Tendsto.congr' (hZ.mono fun N hN => by simp only [hN]) h
57-
58-theorem HasLeadingTerm.add (h : HasLeadingTerm Z c lam k) (h' : HasLeadingTerm Z' c' lam k) :
59-    HasLeadingTerm (fun N => Z N + Z' N) (c + c') lam k := by
60-  refine (Tendsto.add h h').congr' (Eventually.of_forall fun N => ?_)
61-  simp only [add_div]
62-
63-theorem HasLeadingTerm.const_mul (h : HasLeadingTerm Z c lam k) (a : ℝ) :
64-    HasLeadingTerm (fun N => a * Z N) (a * c) lam k := by
65-  refine (Tendsto.const_mul a h).congr' (Eventually.of_forall fun N => ?_)
--
194:theorem hasLeadingTerm_sum_of_extremal (lam₀ : ℝ) (k₀ : ℕ)
195-    (h : ∀ j ∈ s, HasLeadingTerm (Z j) (c j) (lam j) (k j)) (hlam : ∀ j ∈ s, lam₀ ≤ lam j)
196-    (hk : ∀ j ∈ s, lam j = lam₀ → k j ≤ k₀) :
197-    HasLeadingTerm (fun N => ∑ j ∈ s, Z j N)
198-      (∑ j ∈ s.filter (fun j => lam j = lam₀ ∧ k j = k₀), c j) lam₀ k₀ := by
199-  classical
200-  rw [Finset.sum_filter]
201-  refine HasLeadingTerm.sum s fun j hj => ?_
202-  by_cases htie : lam j = lam₀ ∧ k j = k₀
203-  · rw [if_pos htie]
204-    obtain ⟨h1, h2⟩ := htie
205-    have := h j hj
206-    rwa [h1, h2] at this
207-  · rw [if_neg htie]
208-    refine (h j hj).of_dominated ?_
209-    rcases lt_or_eq_of_le (hlam j hj) with hlt | heq
210-    · exact Or.inl hlt
--
309:theorem hasLeadingTerm_boltzmannIntegral (D : ι → Finset (Fin d)) (ε : ℝ)
310-    {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
311-    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
312-    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
313-    (c lam : ι → Finset (Fin d) → ℝ) (k : ι → Finset (Fin d) → ℕ) (lam₀ : ℝ) (k₀ : ℕ)
314-    (hpiece : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
315-      HasLeadingTerm (R.pieceIntegral D ε i I F K p) (c i I) (lam i I) (k i I))
316-    (hlam : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty), lam₀ ≤ lam i I)
317-    (hk : ∀ i, ∀ I ∈ (D i).powerset.filter (fun I => I.Nonempty), lam i I = lam₀ → k i I ≤ k₀)
318-    (hempty : ∀ i, HasLeadingTerm (R.pieceIntegral D ε i ∅ F K p) 0 lam₀ k₀) :
319-    HasLeadingTerm (R.boltzmannIntegral F K p)
320-      (∑ i, ∑ I ∈ ((D i).powerset.filter (fun I => I.Nonempty)).filter
321-        (fun I => lam i I = lam₀ ∧ k i I = k₀), c i I) lam₀ k₀ := by
322-  have hsum := HasLeadingTerm.sum (lam := lam₀) (k := k₀) Finset.univ
323-    (Z := fun i N => (∑ I ∈ (D i).powerset.filter (fun I => I.Nonempty),
324-      R.pieceIntegral D ε i I F K p N) + R.pieceIntegral D ε i ∅ F K p N)
325-    (c := fun i => (∑ I ∈ ((D i).powerset.filter (fun I => I.Nonempty)).filter

568:theorem IsMonomialChart.local_leading_term {dom : Set (Fin d → ℝ)} {e : Fin d →₀ ℕ}
569-    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
570-    (hU : IsOpen U) (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
571-    (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0)
572-    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) (hFpos : 0 < F (φ y₀)) :
573-    ∃ C : CentredChartData K φ h y₀, ∃ Ω : Set (Fin d → ℝ), IsCompact Ω ∧ φ y₀ ∈ Ω ∧
574-      Ω ⊆ φ '' W ∧ Ω ⊆ U ∧ (∃ V : Set (Fin d → ℝ), IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, φ y ∈ Ω) ∧
575-      ∃ c : ℝ, 0 < c ∧
576-        (fun N => ∫ x in Ω, F x * Real.exp (-N * K x)) ~[atTop]
577-          fun N => c * (N ^ (-C.lam) * Real.log N ^ (C.mult - 1)) := by
578-  obtain ⟨C, hC, -⟩ := exists_centredChartData hc hU hK hK0 hy₀W hy₀U hKy₀
579-  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 C.V₀_open 0 C.zero_mem
580-  set ε' := ε / 2 with hε'
581-  have hε'pos : 0 < ε' := half_pos hε
582-  have hcball : Metric.closedBall (0 : Fin d → ℝ) ε' ⊆ C.V₀ :=
583-    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
584-  set j₀ : Fin (C.n + 1) := 0 with hj₀

.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean:46:structure IsMonomialChart (F : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-47-    (dom : Set (Fin n → ℝ)) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)) : Prop where
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-48-  isOpen : IsOpen W
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-49-  subset : dom ⊆ W
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-50-  analyticOnNhd : AnalyticOnNhd ℝ φ W
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-51-  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-52-  exists_unit : ∃ u : (Fin n → ℝ) → ℝ, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-53-    ∀ y ∈ W, F (φ y) = u y * monomialEval y e
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-54-  exists_jacUnit : ∃ v : (Fin n → ℝ) → ℝ, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-55-    ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-56-
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-57-/-- A per-chart predicate: a property of the chart map, its domain and its exceptional set. -/
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-58-abbrev ChartPred (n : ℕ) : Type :=
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-59-  ((Fin n → ℝ) → (Fin n → ℝ)) → Set (Fin n → ℝ) → Set (Fin n → ℝ) → Prop
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-60-
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-61-/-- Atom 9.2.4.e (auxiliary): a chart predicate stable under shrinking the chart domain (with the
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-62-exceptional set cut down to the new domain, as `restrict` does). Source: [derived]. -/
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-63-def ChartPredStable (P : ChartPred n) : Prop :=
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-64-  ∀ (φ : (Fin n → ℝ) → (Fin n → ℝ)) (dom E dom' : Set (Fin n → ℝ)),
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-65-    dom' ⊆ dom → P φ dom E → P φ dom' (E ∩ dom')
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-66-
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-67-namespace PartialResolution
.lake/packages/hironaka/Monomialize/Analytic/Structural/Terminal.lean-68-
