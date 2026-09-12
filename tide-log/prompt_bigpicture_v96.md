# Consult #96 — fundamentals of the certified resolved geometry: after producers 1–2, design units 3–5 and the compatibility layer

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 620 modules, zero sorry/axiom), the companion of the paper *Grammar
(Expectations and the Exceptional Divisor)* (Gerraty–Murfet 2026). Your consult #95 set the programme
"fundamentals of the certified resolved geometry": cores + phase-gap tails as the primary certificate
interface; PRODUCE certificates from series/geometric data; then genuine tubular/divisor compatibility
structures. We have executed its first units. Please (1) audit what landed for honesty and design errors,
(2) give the precise mathematical design of the next units — normal-unit normalisation, the finite
analytic-normal collar decomposition, the general compact-box producer — on the coordinate model, reusing
the existing variable-unit/tubular machinery where its statements suffice (an API audit of that machinery
is included below), and (3) specify the compatibility structures at the level of Lean field lists we can
implement directly.

## 1. What landed since #95 (main `cfcd013`)

* **CCCXVI `CoreNormalMomentRepresentation`.** `CoreNormalMomentPresentation C` (fibre power series `p v`,
  radii `R v > ofReal b`, density bound `cBound`) for a `CorePresentation`; ★★ `AnalyticCoreDecomposition.
  Z_eq_moment_series : D.Z N = Σ_I ∫ Σ'_r (1/r!) ∫ normalJet(obsFibre v) r dμ_{v,N} dν_I + resid N`; adapters
  `ChartPresentation.toCore`, `AdaptedStrataData.toCoreDecomposition` (so the old exact-sublevel route is a
  special case).
* **Refactor.** `ResolvedCertificate` now has `cores : AnalyticCoreDecomposition L M (fun I => ↥(base I)) n β`
  and `T : ∀ I, CoreNormalMomentPresentation (cores.chart I)`; the representation theorem gained `+ cores.resid N`
  with `|resid N| ≤ (∫|obs| d tail) e^{−δ₀N}`; everything downstream (CCCIII–CCCXV) still holds.
* **CCCXVII `AnalyticSeriesFamily`.** For a `b'`-weighted ℓ¹ coefficient family `f` (`Σ|f_γ| b'^{|γ|} < ∞`):
  `HasFPowerSeriesOnBall (evalF f) (polySeriesD f) 0 (ofReal b')` and `jetFamily n (evalF f) = f`; the scaled
  product rule `evalF (f ⋆ g) = evalF f · evalF g` on `0 ≤ u_i ≤ b`.
* **CCCXVIII `CoordinateBoxCoreCertificate` (producer 1).** Namespace `SeriesBox`. Data: `k`, `fϕ fφ : CoeffFamily
  (n+1)` with `AbsSummableAt … b'`, `0 < b < b'`, `hϕ0 : ∀ w ∈ [0,b]^{n+1}, 0 ≤ evalF fϕ w`. Prior/observable are
  defined by a coordinatewise clamp: `prior w = max (evalF fϕ (clamp ((b+b')/2) w)) 0`, `obs w = evalF fφ
  (clamp ((b+b')/2) w)` — globally continuous, equal to the series on the region, analytic at 0 on the ball of
  radius `(b+b')/2 > b`. `locData`: μ = prior-weighted Lebesgue on `[0,b]^{n+1}`, phase `∏ w_i^{2k_i}`. One
  core at the deepest stratum: Dirac base on the origin, `Φ = snd`, `c(s,u) = prior u`, `h = 0`, datum
  `ofFamilies b 0 (fϕ ⋆ fφ)`; `transport` proved EXACTLY (`dirac_prod`, `withDensity_map_of_embedding`),
  tail `μ|_{(0,b]ᶜ} = 0` (region∖box ⊆ coordinate hyperplanes). Then ★★ `certificate : ResolvedCertificate
  (CoordModel.geometry) (CoordModel.normalData) [0,b]^{n+1} phase prior obs`, ★★ `coeffCertificate` (cc = fϕ,
  `jet_abs`/`datum_eq` by `jetFamily_obs`, `toEta_ofFamilies`), ★★★ `hasCoordFreeExpansion_box :
  HasCoordFreeExpansion certificate.stratumMeasure coeffCertificate.field (spectrumLe (latticeQ k) n) …` with
  no certificate hypothesis left; `globalLaplace_region_eq` rewrites the integrand to `evalF fφ · evalF fϕ`.
* **CCCXIX `ParameterisedSeriesDatum` (producer 2).** `UniformSeriesFamily X d b'` (fields `f : X → CoeffFamily
  d`, `M`, `continuous_coeff : ∀ γ, Continuous (f · γ)`, `abs_le : |f x γ| ≤ M γ`, `M_abs : AbsSummableAt M b'`);
  `conv` (majorant `M ⋆ M'`); ★ `continuous_datum : Continuous (fun x => ofFamilies b 0 (f x))` in the ℓ¹
  topology of `DataSpace d` (majorant criterion), `datumC : C(X, DataSpace d)`; Weierstrass package
  `continuous_evalF_clamp`/`continuousOn_evalF` on `X × [−r,r]^d`, `abs_evalF_le`, `evalF_conv`.

Key declarations (verbatim signatures):

### Grammar/ResolvedMomentRepresentation.lean
```lean
structure ResolvedCertificate (R : ResolvedGeometry d U) (D : ResolvedNormalData R A)
    (W : Set (Fin d → ℝ)) (K ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- The localisation datum on the resolved space. -/
  L : LocalisationData U
  obs_eq : L.obs = φ ∘ R.π
  phase_eq : L.phase = K ∘ R.π
  /-- The resolved measure pushes forward to the prior-weighted Lebesgue measure on `W`. -/
  transport : L.μ.map R.π = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w)
  /-- The number of pieces. -/
  M : ℕ
  /-- The normal dimensions minus one. -/
  n : Fin M → ℕ
  /-- The stratum presented by each piece. -/
  strat : Fin M → Finset R.Component
  /-- The compact piece of the stratum carrying the base measure (the support of the adapted
  partition weight). -/
  base : ∀ I, Set (R.Stratum (strat I))
  isCompact_base : ∀ I, IsCompact (base I)
  /-- The inverse temperature of the normal form. -/
  β : ℝ
  β_pos : 0 < β
  /-- The analytic core decomposition (cores with a phase-gap tail), with the compact stratum
  pieces as base spaces. -/
  cores : AnalyticCoreDecomposition L M (fun I => ↥(base I)) n β
  /-- The normal-moment presentations (analytic fibre observables). -/
  T : ∀ I, CoreNormalMomentPresentation (cores.chart I)
  /-- The frames `ℝ^{n_I+1} ≃ N_s` identifying box normal coordinates with the normal space. -/
  frame : ∀ I (s : ↥(base I)), (Fin (n I + 1) → ℝ) ≃L[ℝ] D.N (strat I) s.1
  /-- The box parametrisation is the tubular germ in the frame. -/
  Φ_eq : ∀ I (s : ↥(base I)) (u : Fin (n I + 1) → ℝ),
    (cores.chart I).Φ (s, u) = D.Φ (strat I) s.1 (frame I s u)

theorem obsFibre_eq (I : Fin C.M) (s : ↥(C.base I)) (u : Fin (C.n I + 1) → ℝ) :
    (C.cores.chart I).obsFibre s u = φ (R.π (D.Φ (C.strat I) s.1 (C.frame I s u))) := by

noncomputable def normalFibreMeasure (I : Fin C.M) (s : ↥(C.base I)) (N : ℝ) :
    Measure (D.N (C.strat I) s.1) :=

theorem integrable_norm_pow_normalFibreMeasure (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N)
    (s : ↥(C.base I)) (r : ℕ) :
    Integrable (fun ξ : D.N (C.strat I) s.1 => ‖ξ‖ ^ r) (C.normalFibreMeasure I s N) :=

noncomputable def exactMoment (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N) (s : ↥(C.base I))
    (r : ℕ) : MomentTensor (D.N (C.strat I) s.1) r :=

theorem pair_exactMoment_normalDifferential (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N)
    (s : ↥(C.base I)) (r : ℕ) :
    (C.exactMoment I hN s r).pair (D.normalDifferential φ (C.strat I) s.1 r) =
      ∫ u, normalJet ((C.cores.chart I).obsFibre s) r (fun _ => u)
        ∂(C.cores.chart I).fibreMeasure s N := by

theorem globalLaplace_eq_Z (N : ℝ) :
    globalLaplace W K (fun w => φ w * ϕ w) N = C.L.Z N := by

theorem globalLaplace_eq_tsum_stratumContraction {N : ℝ} (hN : 0 ≤ N) :
    globalLaplace W K (fun w => φ w * ϕ w) N =
      ∑ I, (∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
        (C.exactMoment I hN s r).pair (D.normalDifferential φ (C.strat I) s.1 r) ∂C.cores.ν I) +
      C.cores.resid N := by

theorem abs_resid_le {N : ℝ} (hN : 0 ≤ N) :
    |C.cores.resid N| ≤ (∫ z, |C.L.obs z| ∂C.cores.tail) * Real.exp (-C.cores.δ₀ * N) :=

theorem cutoffExpansion_globalLaplace :
    CutoffExpansion (commonQ C.cores.k) (commonD C.n) (globalLaplace W K fun w => φ w * ϕ w)
      (gCoeff C.cores.ν C.cores.h C.cores.k C.β C.cores.b C.cores.x) := by

theorem cutoffExpansion_stratumContraction :
    CutoffExpansion (commonQ C.cores.k) (commonD C.n)
      (fun N => ∑ I, ∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
        ∫ u, normalJet ((C.cores.chart I).obsFibre s) r (fun _ => u)
          ∂(C.cores.chart I).fibreMeasure s N ∂C.cores.ν I)
      (gCoeff C.cores.ν C.cores.h C.cores.k C.β C.cores.b C.cores.x) :=

```

### Grammar/CoreNormalMomentRepresentation.lean
```lean
def obsFibre (v : K) (u : Fin (n + 1) → ℝ) : ℝ := D.obs (C.Φ (v, u))

noncomputable def fibreMeasure (v : K) (N : ℝ) : Measure (Fin (n + 1) → ℝ) :=

theorem fibreMeasure_ac (v : K) (N : ℝ) :
    C.fibreMeasure v N ≪ dressedMeasure n C.h C.k β N C.b :=

theorem fibreMeasure_ae_norm_le (v : K) (N : ℝ) : ∀ᵐ u ∂C.fibreMeasure v N, ‖u‖ ≤ C.b :=

structure CoreNormalMomentPresentation {U : Type*} [MeasurableSpace U] {D : LocalisationData U}
    {target : Measure U} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}
    (C : CorePresentation D target K n β) where
  /-- the fibre power series of the observable -/
  p : K → FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ
  /-- the fibre radii -/
  R : K → ℝ≥0∞
  analytic : ∀ v, HasFPowerSeriesOnBall (C.obsFibre v) (p v) 0 (R v)
  radius : ∀ v, ENNReal.ofReal C.b < R v
  /-- a bound for the density factor -/
  cBound : ℝ
  c_le : ∀ q, C.c q ≤ cBound

theorem isFiniteMeasure_fibreMeasure (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    IsFiniteMeasure (C.fibreMeasure v N) := by

theorem integrable_norm_pow_fibre (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) (r : ℕ) :
    Integrable (fun u => ‖u‖ ^ r) (C.fibreMeasure v N) :=

theorem integral_obsFibre_eq_tsum (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) (v : K) :
    ∫ u, C.obsFibre v u ∂C.fibreMeasure v N = ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N := by

theorem tanIntegral_eq_moment_series (hβ : 0 ≤ β) {N : ℝ} (hN : 0 ≤ N) :
    tanIntegral C.ν n C.h C.k β N C.b C.x = ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet (C.obsFibre v) r (fun _ => u) ∂C.fibreMeasure v N ∂C.ν := by

theorem Z_eq_moment_series (T : ∀ I, CoreNormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.resid N := by

theorem momentSeries_cutoffExpansion (T : ∀ I, CoreNormalMomentPresentation (A.chart I))
    (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) := by

theorem expectation_expansion_of_analyticCoreDecomposition
    (T : ∀ I, CoreNormalMomentPresentation (A.chart I)) (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) ∧
    (∀ N, 0 ≤ N → |A.resid N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N)) ∧
    (∀ N, 0 ≤ N → D.Z N = ∑ I, (∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) + A.resid N) ∧
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u) ∂(A.chart I).fibreMeasure v N
        ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) :=

def ChartPresentation.toCore (C : ChartPresentation D ρ K n β) :
    CorePresentation D ((D.μ.restrict D.sublevel).withDensity fun z =>
      ((ρ z).toNNReal : ℝ≥0∞)) K n β where

def NormalMomentPresentation.toCore {C : ChartPresentation D ρ K n β}
    (T : NormalMomentPresentation C) : CoreNormalMomentPresentation C.toCore where

theorem withDensity_finsetSum {ι : Type*} (s : Finset ι) (μ : Measure U) {f : ι → U → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, μ.withDensity (f i) := by

noncomputable def AdaptedStrataData.toCoreDecomposition (A : AdaptedStrataData D M K' n' β) :
    AnalyticCoreDecomposition D M K' n' β where

theorem AdaptedStrataData.toCoreDecomposition_chart (A : AdaptedStrataData D M K' n' β)
    (I : Fin M) : A.toCoreDecomposition.chart I = (A.chart I).toCore := rfl

```

### Grammar/AnalyticCorePresentation.lean
```lean
structure CorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ)
    where
  /-- the base measure on the compact stratum piece -/
  ν : Measure K
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the normal exponents of the Jacobian -/
  h : Fin (n + 1) → ℕ
  /-- the normal exponents of the phase, all positive -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the chart map into the resolved space -/
  Φ : K × (Fin (n + 1) → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the density factor (prior, Jacobian unit, tangential cutoff) -/
  c : K × (Fin (n + 1) → ℝ) → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p
  /-- the tangential datum realising the amplitude -/
  x : TangentialData K (n + 1)
  transport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity h c p).toNNReal : ENNReal)).map Φ = target
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b,
    CoeffFamily.evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)
  fluct_zero : ∀ v, xiCoord (x v) = 0

theorem measurable_chartDensity : Measurable (chartDensity C.h C.c) :=

theorem chartDensity_nonneg : ∀ᵐ p ∂chartMeasure C.ν n C.b, 0 ≤ chartDensity C.h C.c p := by

noncomputable def boxIntegrand (N : ℝ) (p : K × (Fin (n + 1) → ℝ)) : ℝ :=

theorem integral_boxIntegrand (N : ℝ) (v : K) :
    ∫ u in piBox (n + 1) (Ioc 0 C.b), C.boxIntegrand N (v, u) =
      dataBoxIntegral n C.h C.k β N C.b (C.x v) := rfl

theorem density_smul_eq_boxIntegrand (N : ℝ) :
    ∀ᵐ p ∂chartMeasure C.ν n C.b,
      (chartDensity C.h C.c p).toNNReal • D.integrand N (C.Φ p) = C.boxIntegrand N p := by

theorem integral_eq_tanIntegral (N : ℝ) (hint : Integrable (D.integrand N) target) :
    ∫ z, D.integrand N z ∂target = tanIntegral C.ν n C.h C.k β N C.b C.x := by

structure AnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
    (n : Fin M → ℕ) (β : ℝ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the core presentations -/
  chart : ∀ I, CorePresentation D (core I) (K I) (n I) β

noncomputable def ν (I : Fin M) : Measure (K I) := (A.chart I).ν

def h (I : Fin M) : Fin (n I + 1) → ℕ := (A.chart I).h

def k (I : Fin M) : Fin (n I + 1) → ℕ := (A.chart I).k

def b (I : Fin M) : ℝ := (A.chart I).b

def x : JointData K n := fun I => (A.chart I).x

theorem k_pos : ∀ I i, 0 < A.k I i := fun I => (A.chart I).k_pos

theorem b_pos : ∀ I, 0 < A.b I := fun I => (A.chart I).b_pos

theorem core_le (I : Fin M) : A.core I ≤ D.μ := by

theorem tail_le : A.tail ≤ D.μ := by

noncomputable def tailInt (N : ℝ) : ℝ := ∫ z, D.integrand N z ∂A.tail

noncomputable def resid (N : ℝ) : ℝ := D.Z N - gInt A.ν A.h A.k β A.b A.x N

theorem Z_eq (N : ℝ) : D.Z N = gInt A.ν A.h A.k β A.b A.x N + A.resid N := by

theorem Z_eq_gInt_add_tailInt {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = gInt A.ν A.h A.k β A.b A.x N + A.tailInt N := by

theorem resid_eq {N : ℝ} (hN : 0 ≤ N) : A.resid N = A.tailInt N := by

theorem tailInt_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.tailInt N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N) := by

theorem resid_bound {N : ℝ} (hN : 0 ≤ N) :
    |A.resid N| ≤ (∫ z, |D.obs z| ∂A.tail) * Real.exp (-A.δ₀ * N) := by

theorem resid_tendsto {ε : ℝ} (hε : ε < A.δ₀) :
    Tendsto (fun N => A.resid N * Real.exp (ε * N)) atTop (𝓝 0) :=

theorem first_nonzero (hβ : 0 < β) {L : ℝ}
    (hne : ∃ p ∈ indexSet (commonD n) (commonQ A.k) L, gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible (commonD n) (commonQ A.k) ∧
      gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible (commonD n) (commonQ A.k), precedes q p →
        gCoeff A.ν A.h A.k β A.b A.x q.1 q.2 = 0) ∧
      D.Z ~[atTop] fun N => gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 *
        (N ^ (-p.1) * Real.log N ^ p.2) :=

theorem flat (hβ : 0 < β)
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ A.k), gCoeff A.ν A.h A.k β A.b A.x p.1 p.2 = 0)
    (L : ℝ) : Tendsto (fun N => D.Z N / N ^ (-L)) atTop (𝓝 0) :=

theorem cutoffExpansion (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) := by

theorem expansion (hβ : 0 < β) (L : ℝ) (hL : 0 < L) : ∃ Kc : ℝ, ∀ᶠ N in atTop,
    |D.Z N - absSpectralSum (commonQ A.k) (commonD n) (gCoeff A.ν A.h A.k β A.b A.x) L N| ≤
      Kc * (N ^ (-L) * (1 + Real.log N) ^ commonD n) :=

def HasAnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (β : ℝ) : Prop :=

theorem cutoffExpansion_of_hasAnalyticCoreDecomposition {U : Type*} [MeasurableSpace U]
    {D : LocalisationData U} {β : ℝ} (hβ : 0 < β) (h : HasAnalyticCoreDecomposition D β) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧ CutoffExpansion Q Dg D.Z c := by

noncomputable def cubeLocalisationData {d : ℕ} (K F : (Fin d → ℝ) → ℝ) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) (w : Fin d → ℝ) (r : ℝ)
    (hFr : Integrable F (volume.restrict (Metric.closedBall w r))) (δ : ℝ) (hδ : 0 < δ) :
    LocalisationData (Fin d → ℝ) where

def CompatibleDivisorLocalisation (d : ℕ) : Prop :=

```

### Grammar/CoordinateBoxCoreCertificate.lean
```lean
noncomputable def clamp (r : ℝ) (hr : 0 ≤ r) (u : Fin d → ℝ) : Fin d → ℝ :=

noncomputable def evalFClamp (f : CoeffFamily d) (r : ℝ) (hr : 0 ≤ r) : (Fin d → ℝ) → ℝ :=

theorem hasFPowerSeriesOnBall_evalFClamp :
    HasFPowerSeriesOnBall (evalFClamp f r hr.le) (polySeriesD f) 0 (ENNReal.ofReal r) := by

theorem jetFamily_evalFClamp {n : ℕ} (f : CoeffFamily (n + 1)) {b' : ℝ} (hb' : 0 < b')
    (hf : AbsSummableAt f b') {r : ℝ} (hr : 0 < r) (hrb' : r < b') :
    jetFamily n (evalFClamp f r hr.le) = f := by

theorem AbsSummableAt.mono {d : ℕ} {f : CoeffFamily d} {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b')
    (hf : AbsSummableAt f b') : AbsSummableAt f b :=

theorem withDensity_map_of_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {e : α → β} (he : MeasurableEmbedding e) (μ : Measure α) (g : β → ℝ≥0∞) :
    (μ.map e).withDensity g = (μ.withDensity (g ∘ e)).map e := by

noncomputable def rmid : ℝ := (b + b') / 2

theorem b_lt_rmid : b < rmid b b' := by unfold rmid; linarith

noncomputable def obs : (Fin (n + 1) → ℝ) → ℝ :=

noncomputable def prior : (Fin (n + 1) → ℝ) → ℝ :=

def hh : Fin (n + 1) → ℕ := fun _ => 0

def region : Set (Fin (n + 1) → ℝ) := piBox (n + 1) (Icc 0 b)

def box : Set (Fin (n + 1) → ℝ) := piBox (n + 1) (Ioc 0 b)

theorem volume_region_diff_box : volume (region n b \ box n b) = 0 := by

theorem hasFPowerSeriesOnBall_obs :
    HasFPowerSeriesOnBall (obs n fφ b b' hb hbb') (polySeriesD fφ) 0
      (ENNReal.ofReal (rmid b b')) :=

theorem jetFamily_obs : jetFamily n (obs n fφ b b' hb hbb') = fφ :=

noncomputable abbrev geometry : ResolvedGeometry (n + 1) (Fin (n + 1) → ℝ) :=

noncomputable abbrev normalData : ResolvedNormalData (geometry n k hk) (Amb (n + 1)) :=

abbrev phase : (Fin (n + 1) → ℝ) → ℝ := CoordModel.phase (n + 1) k

noncomputable def locData : LocalisationData (Fin (n + 1) → ℝ) where

abbrev Base := ↥(Set.univ : Set ((geometry n k hk).Stratum Finset.univ))

def basePt : Base n k hk := ⟨origin (n + 1) k (hh n) hk, trivial⟩

noncomputable def datum : DataSpace (n + 1) :=

noncomputable def core :
    CorePresentation (locData n k fϕ fφ b b' hb hbb' hϕ hφ)
      ((locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)) (Base n k hk) n 1 where

theorem restrict_box_compl_eq_zero :
    (locData n k fϕ fφ b b' hb hbb' hϕ hφ).μ.restrict (box n b)ᶜ = 0 := by

noncomputable def coreDecomposition :
    AnalyticCoreDecomposition (locData n k fϕ fφ b b' hb hbb' hϕ hφ) 1 (fun _ => Base n k hk)
      (fun _ => n) 1 where

noncomputable def presentation :
    CoreNormalMomentPresentation (core n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0) where

noncomputable def certificate :
    ResolvedCertificate (geometry n k hk) (normalData n k hk) (region n b) (phase n k)
      (prior n fϕ b b' hb hbb') (obs n fφ b b' hb hbb') where

noncomputable def coeffCertificate :
    (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).CoefficientCertificate where

theorem commonQ_certificate :
    commonQ (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).cores.k = latticeQ k := by

theorem commonD_certificate :
    commonD (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).n = n := by

theorem hasCoordFreeExpansion_box :
    (normalData n k hk).HasCoordFreeExpansion
      (certificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).stratumMeasure
      (coeffCertificate n k hk fϕ fφ b b' hb hbb' hϕ hφ hϕ0).field
      (spectrumLe (latticeQ k) n) (region n b) (phase n k) (prior n fϕ b b' hb hbb')
      (obs n fφ b b' hb hbb') := by

theorem globalLaplace_region_eq (N : ℝ) :
    globalLaplace (region n b) (phase n k)
      (fun w => obs n fφ b b' hb hbb' w * prior n fϕ b b' hb hbb' w) N =
      ∫ w in region n b, evalF fφ w * evalF fϕ w * Real.exp (-N * ∏ i, w i ^ (2 * k i)) := by

```

### Grammar/ParameterisedSeriesDatum.lean
```lean
structure UniformSeriesFamily (X : Type*) [TopologicalSpace X] (d : ℕ) (b' : ℝ) where
  /-- The coefficient family at the parameter `x`. -/
  f : X → CoeffFamily d
  /-- The uniform majorant. -/
  M : CoeffFamily d
  continuous_coeff : ∀ γ, Continuous fun x => f x γ
  abs_le : ∀ x γ, |f x γ| ≤ M γ
  M_abs : AbsSummableAt M b'

theorem absSummableAt (hb' : 0 ≤ b') (x : X) : AbsSummableAt (F.f x) b' := by

theorem absSummableAt_of_le {b : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') (x : X) :
    AbsSummableAt (F.f x) b :=

theorem M_absSummableAt_of_le {b : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') : AbsSummableAt F.M b :=

theorem conv_le_conv {c c' e e' : CoeffFamily d} (hc : ∀ γ, 0 ≤ c γ) (he : ∀ γ, 0 ≤ e γ)
    (hcc : ∀ γ, c γ ≤ c' γ) (hee : ∀ γ, e γ ≤ e' γ) (γ : Fin d → ℕ) :
    CoeffFamily.conv c e γ ≤ CoeffFamily.conv c' e' γ :=

noncomputable def conv (hb' : 0 ≤ b') (G : UniformSeriesFamily X d b') :
    UniformSeriesFamily X d b' where

noncomputable def datum (x : X) : DataSpace d :=

noncomputable def dataMajorant : DataIdx d → ℝ :=

noncomputable def datumC : C(X, DataSpace d) := ⟨F.datum hb hbb', F.continuous_datum hb hbb'⟩

theorem continuousOn_evalF {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') :
    ContinuousOn (fun p : X × (Fin d → ℝ) => evalF (F.f p.1) p.2)
      (univ ×ˢ piBox d (Icc (-r) r)) := by

theorem abs_evalF_le {r : ℝ} (hr : 0 ≤ r) (hrb' : r ≤ b') (x : X) (u : Fin d → ℝ)
    (hu : ∀ i, |u i| ≤ r) :
    |evalF (F.f x) u| ≤ ∑' γ, F.M γ * r ^ (∑ i, γ i) := by

theorem hasFPowerSeriesOnBall_evalFClamp {r : ℝ} (hb' : 0 < b') (hr : 0 < r) (hrb' : r < b')
    (x : X) :
    HasFPowerSeriesOnBall (evalFClamp (F.f x) r hr.le) (polySeriesD (F.f x)) 0
      (ENNReal.ofReal r) :=

theorem jetFamily_evalFClamp {n : ℕ} (F : UniformSeriesFamily X (n + 1) b') {r : ℝ}
    (hb' : 0 < b') (hr : 0 < r) (hrb' : r < b') (x : X) :
    jetFamily n (evalFClamp (F.f x) r hr.le) = F.f x :=

theorem evalF_conv (G : UniformSeriesFamily X d b') (x : X) {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ b) :
    evalF (toEta b ((F.conv (hb.le.trans hbb') G).datum hb hbb' x)) u =
      evalF (F.f x) u * evalF (G.f x) u := by

```

### Grammar/AnalyticSeriesFamily.lean
```lean
theorem hasFPowerSeriesOnBall_evalF :
    HasFPowerSeriesOnBall (evalF f) (polySeriesD f) 0 (ENNReal.ofReal b') where

theorem jetFamily_evalF {n : ℕ} (f : CoeffFamily (n + 1)) {b' : ℝ} (hb' : 0 < b')
    (hf : AbsSummableAt f b') : jetFamily n (evalF f) = f := by

theorem evalF_conv_of_absSummableAt {f g : CoeffFamily d} {b : ℝ} (hb : 0 < b)
    (hf : AbsSummableAt f b) (hg : AbsSummableAt g b) {u : Fin d → ℝ}
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ b) :
    evalF (CoeffFamily.conv f g) u = evalF f u * evalF g u := by

```

Headline rows (verbatim) for CCCXVI–CCCXIX:

| **CCCXIX** | ★ **PARAMETERISED SERIES DATA ARE CONTINUOUS INTO THE DATA SPACE (u637; consult #95 producer unit 3)**: `UniformSeriesFamily X d b'` = a family `x ↦ f x` of coefficient families over a topological parameter space with coordinatewise continuity and a UNIFORM weighted-ℓ¹ majorant `|f x γ| ≤ M γ`, `Σ M_γ b'^{|γ|} < ∞` (the real form of a uniform analytic extension/bound on a larger normal polydisc). Each fibre is `b'`-summable (`absSummableAt`), the Cauchy product of uniform families is uniform with majorant `M ⋆ M'` (`conv`, via `conv_le_conv`), and ★ the weighted datum `x ↦ ofFamilies b 0 (f x)` is CONTINUOUS in the ℓ¹ topology of `DataSpace d` (`continuous_datum`, by the `LpContinuity` majorant criterion with `M_γ b^{|γ|}`) — bundled as `datumC : C(X, DataSpace d)` with `toEta_datumC = f x`, `toXi_datumC = 0`, i.e. the `x` field of a `CorePresentation` over a compact base produced from series data, meeting Astra's gate (continuity in the actual `DataSpace` topology, not coefficientwise). Also the Weierstrass M-test package for the evaluated series: `continuous_evalF_clamp`/`continuousOn_evalF` (joint continuity of `(x,u) ↦ evalF (f x) u` on `X × [−r,r]^d`), `abs_evalF_le : |evalF (f x) u| ≤ Σ M_γ r^{|γ|}` (the uniform `cBound`), per-fibre analyticity `hasFPowerSeriesOnBall_evalFClamp`/`jetFamily_evalFClamp`, and the product amplitude identity `evalF_conv` on `[0,b]^d`. Axiom-clean | ParameterisedSeriesDatum.lean |
| **CCCXVIII** | ★★★ **CERTIFICATE PRODUCER: SERIES DATA ON THE COORDINATE BOX (u636; consult #95 unit 2 `CoordinateBoxCoreCertificate`)**: for `b'`-weighted ℓ¹ prior/observable coefficient families `fϕ, fφ` (with `fϕ` nonnegative on the box), `b < b'`, and exponents `k`, the module PRODUCES — rather than assumes — the resolved certificate on the coordinate model `∏ u_i^{2k_i}` on `[0,b]^{n+1}`: `SeriesBox.locData` (prior-weighted Lebesgue measure on the region), a single `SeriesBox.core` at the deepest stratum (Dirac base, normal box `(0,b]^{n+1}`, `Φ = snd`, density `ϕ`, `h = 0`, amplitude datum `fϕ ⋆ fφ`; the `transport` field is proved exactly via `dirac_prod`/`withDensity_map_of_embedding`), a one-core `SeriesBox.coreDecomposition` with NULL tail (`restrict_box_compl_eq_zero`: the region minus the open box lies in the coordinate hyperplanes), the normal-moment presentation `SeriesBox.presentation` from the observable's power series (radius `(b+b')/2 > b`), and ★★ `SeriesBox.certificate : ResolvedCertificate …` with `Φ_eq` checked against `frameUniv`; ★★ `SeriesBox.coeffCertificate` has density family `cc = fϕ` and `jet_abs`/`datum_eq` discharged by `jetFamily_obs` + `toEta_ofFamilies`. Hence ★★★ `SeriesBox.hasCoordFreeExpansion_box : HasCoordFreeExpansion certificate.stratumMeasure coeffCertificate.field (spectrumLe (latticeQ k) n) (region n b) (phase n k) prior obs` — the coordinate-free expansion of `∫_{[0,b]^{n+1}} φ ϕ e^{−N ∏u^{2k}}` (`globalLaplace_region_eq` rewrites the integrand to the genuine series `evalF fφ · evalF fϕ`) with NO certificate hypotheses left: every field is constructed from the series data. Prior and observable are defined via a coordinatewise clamp (`evalFClamp`) so they are globally continuous, equal to the series on the region, and analytic at 0 on the larger ball. Also `AbsSummableAt.mono`, `withDensity_map_of_embedding`. Axiom-clean | CoordinateBoxCoreCertificate.lean |
| **CCCXVII** | ★ **WEIGHTED-ℓ¹ COEFFICIENT FAMILIES DEFINE ANALYTIC FUNCTIONS ON THE BOX (u635; consult #95 unit 2 analytic input)**: `norm_monomialForm_le_one`, `norm_symMonomial_le_one`; for a `b'`-weighted ℓ¹ family `f`, `‖polySeriesD f m‖ b'^m ≤ Σ'|f_γ| b'^{|γ|}` (`norm_polySeriesD_le`), `le_radius_polySeriesD`, and ★ `hasFPowerSeriesOnBall_evalF : HasFPowerSeriesOnBall (evalF f) (polySeriesD f) 0 (ofReal b')` (degree fibration of the absolutely convergent monomial series); hence ★ `jetFamily_evalF : jetFamily n (evalF f) = f` — the Taylor family of a general series observable is its coefficient family; `evalF_conv_of_absSummableAt`: the scaled product rule `evalF (f ⋆ g) = evalF f · evalF g` on `0 ≤ u_i ≤ b`. These are exactly the analytic inputs of a coefficient certificate for series data on a box of side `b < b'`. Axiom-clean | AnalyticSeriesFamily.lean |
| **CCCXVI** | ★★ **THE MOMENT REPRESENTATION FOR CORE PRESENTATIONS; THE SUBLEVEL PARTITION IS A SPECIAL CASE (u634; consult #95 unit 1)**: `CorePresentation.obsFibre/fibreMeasure`, `CoreNormalMomentPresentation`, `integral_obsFibre_eq_tsum`, `tanIntegral_eq_moment_series` (the moment argument never used the transport target); ★★ `AnalyticCoreDecomposition.Z_eq_moment_series`: `Z(N) = Σ_I ∫_{K_I} Σ'_r (1/r!)⟨M_{I,r}(N), D^r(F∘Φ_I)⟩ dν_I + resid(N)` with `|resid| ≤ (∫|F| d tail) e^{−δ₀N}`; `momentSeries_cutoffExpansion`; `expectation_expansion_of_analyticCoreDecomposition` — the conditional geometric main theorem for CORES (cores with arbitrary targets + a tail with a positive phase gap: no sublevel-set partition, hence no obstruction for curved sublevel sets, `LocalisationObstruction`); adapters `ChartPresentation.toCore`, `NormalMomentPresentation.toCore`, ★ `AdaptedStrataData.toCoreDecomposition` (cores = weighted sublevel restrictions, tail = `μ|_{K≥δ}`; measure identity from `Σρ_I = 1` a.e. on the sublevel set, `withDensity_finsetSum`). The core interface becomes the primary certificate interface. Axiom-clean | CoreNormalMomentRepresentation.lean |

## 2. API audit of the existing variable-unit / tubular machinery (statements verbatim, proofs omitted)

### 2.1 `VariableUnitKernel.lean`
Purpose: the box kernel with a phase unit `u(z,v)` depending on the normal coordinates,
`varBoxKernel z N = ∫_{(0,b]^{n+1}} A(z,v) ∏ v^h e^{−N u(z,v) ∏ v^{2k}} dv`, and its face coefficient
`varBoxFaceCoeff = boxFaceCoeff` of `A · u^{−λ}` (unit frozen on the minimal face by `faceProj`). No structures.
```lean
noncomputable def varBoxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ v in piBox (n + 1) (Ioc 0 b),
    A z v * (∏ i, v i ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))
noncomputable def varBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  boxFaceCoeff n h k 1 b (fun z v => A z v * u z v ^ (-l)) l z
theorem varBoxKernel_anti_unit … (hle : ∀ v ∈ piBox (n + 1) (Ioc 0 b), A z v ≠ 0 → u₁ z v ≤ u₂ z v) {N : ℝ} (hN : 0 ≤ N) :
    varBoxKernel n h k b u₂ A z N ≤ varBoxKernel n h k b u₁ A z N
theorem abs_varBoxKernel_le_const (hb : 0 < b) … : |varBoxKernel n h k b u A z N| ≤ M * b ^ (∑ i, h i) * b ^ (n + 1)
theorem integrableOn_mul_varBoxKernel … : IntegrableOn (fun z => βw z * varBoxKernel n h k b u A z N) T
```

### 2.2 `VariableUnitCertificate.lean` (★★ CCLV)
Leading term of the variable-unit box kernel for positive continuous `u(z,v)` and continuous signed amplitude;
the unit is frozen on the minimal face. No structures.
```lean
theorem hasLeadingTerm_varBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) {z : Fin t → ℝ}
    {a B : ℝ} (ha : 0 < a) (hab : ∀ v ∈ piBox (n + 1) (Icc 0 b), a ≤ u z v ∧ u z v ≤ B) :
    HasLeadingTerm (varBoxKernel n h k b u A z) (varBoxFaceCoeff n h k b u A l z) l
      (multCount (ratioExp h k) l - 1)
theorem hasLeadingTerm_integral_varBoxKernel … {T : Set (Fin t → ℝ)} (hT : IsCompact T) …
    (hu_pos : ∀ z ∈ T, ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 < u z v) {βw} (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * varBoxKernel n h k b u A z N)
      (∫ z in T, βw z * varBoxFaceCoeff n h k b u A l z) l (multCount (ratioExp h k) l - 1)
```

### 2.3 `ProductChartVar.lean` (★★ CCLX) — product charts with normal-dependent units
```lean
structure ProductMonomialChartVar {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)
    (i : ι) (K : (Fin d → ℝ) → ℝ) where
  e : Fin d →₀ ℕ
  h : Fin d →₀ ℕ
  W : Set (Fin d → ℝ)
  W_open : IsOpen W
  dom_subset : (R.chart i).dom ⊆ W
  monomial : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W
  u : (Fin d → ℝ) → ℝ
  u_cont : ContinuousOn u W
  u_ne : ∀ y ∈ W, u y ≠ 0
  phase_eq : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e
  v : (Fin d → ℝ) → ℝ
  v_cont : ContinuousOn v W
  det_eq : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h
  T : Set (Fin d → ℝ)
  T_compact : IsCompact T
  T_nonempty : T.Nonempty
  T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  b : ℝ
  b_pos : 0 < b
  dom_eq : (R.chart i).dom = productDom e.support T b
  r : (Fin d → ℝ) → ℝ
  r_meas : Measurable r
  Cr : ℝ
  r_bound : ∀ x, |r x| ≤ Cr
  weight_eq : ∀ y ∈ (R.chart i).dom, R.weight i ((R.chart i).Φ y) = r (zeroOn e.support y)
```
Headlines: `hasLeadingTerm_boltzmannIntegral_of_productChartsV`, ★★ `boltzmannIntegral_isEquivalent_of_productChartsV_extremal`
(leading pair `(coverLamV, coverDegV)` with positive coefficient under a dominant-face positivity hypothesis);
`VarUnitCell.coeff_eq_frozen_of_all_minimal`; the amplitude factorisation `amp z n * F(φ(planeSplit (z,n))) = A' z n * ∏ a |n a|^{normalExp}`
is an existential `IsVarPieceAtlasData`. Section hypotheses: `hK0 : ∀ x, 0 ≤ K x`, `hε : 0 < ε`, `hεb : ∀ i, ε ≤ (Ps i).b`,
continuity of `F∘φ`, `p.w∘φ` on `W`, `hF : Integrable (F·p.w)` on `⋃ R.image i`, `hK : Measurable K`.
`ProductChartVarCompat.productCoeffV_toVar_eq`: under `unit_indep` this reproduces the scalar theory exactly.

### 2.4 `MonomialChartProductBox.lean` (★ CCLXX)
```lean
noncomputable def restrictExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) : Fin d →₀ ℕ := e.filter (· ∈ J)
noncomputable def removedExp (e : Fin d →₀ ℕ) (J : Finset (Fin d)) : Fin d →₀ ℕ := e.filter (· ∉ J)
def restrictNhd (e : Fin d →₀ ℕ) (J : Finset (Fin d)) (W : Set (Fin d → ℝ)) : Set (Fin d → ℝ)
noncomputable def divisorSet (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) : Finset (Fin d)
def boxBase (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ)
def productBox (e : Fin d →₀ ℕ) (y₀ : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ)
noncomputable def IsMonomialChart.boxChart : ResolutionChart d  -- dom := productBox e y₀ ρ
noncomputable def IsMonomialChart.boxPackage :
    ProductMonomialChartVar (ResolutionCover.ofChart (IsMonomialChart.boxChart hc hρ hball)) () K
  -- e := restrictExp e (divisorSet e y₀); T := boxBase e y₀ ρ; b := ρ; r := 1; unit u y = (chart unit) y * monomialEval y (removedExp e (divisorSet e y₀))
theorem exists_closedBall_subset_restrictNhd (hW : IsOpen W) (e) (hy₀ : y₀ ∈ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall y₀ ρ ⊆ restrictNhd e (divisorSet e y₀) W
```
This is the only constructor from a hironaka `IsMonomialChart` into the product package (one chart per point; the
off-divisor active factors are absorbed into the unit).

### 2.5 `TubularJacobian.lean`
Over a model graph chart `C` of a compact analytic LCI stratum, `tubeChart C (z,n) = emb z + rowFrame A C.i (emb z) n`
on `tubeChartDom T C = {p | p.1 ∈ C.W ∧ ‖rowFrame … p.2‖ < T.eps}`:
```lean
noncomputable def tubeJac (C : ModelGraphChart A s) (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : ℝ :=
  |(fderiv ℝ (flatChart C) (C.concat p)).det|
theorem integral_tubeChart_image (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {B : Set ((Fin (d - r) → ℝ) × (Fin r → ℝ))} (hB : MeasurableSet B) (hBΩ : B ⊆ tubeChartDom T C)
    (F : (Fin d → ℝ) → ℝ) :
    ∫ y in tubeChart C '' B, F y = ∫ p in B, tubeJac C p • F (tubeChart C p)
theorem integral_tube_piece (T) (C) (F) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y = ∫ p in tubeChartDom T C, tubeJac C p • F (tubeChart C p)
theorem tubeJac_pos (T : AnalyticNormalTubularChart A.normal S) (C) (hp : p ∈ tubeChartDom …) : 0 < tubeJac C p
theorem analyticAt_tubeJac (T : AnalyticNormalTubularChart A.normal S) (C) (hp) : AnalyticAt ℝ (tubeJac C) p
```
Ambient Lebesgue pull-back only; no fibre-integrated (pushforward-of-measure) form.

### 2.6 `TubularBridge.lean`
```lean
structure LiftedFoot (T : NormalTubularChart N S) (emb : B → (Fin d → ℝ)) {ι : Type*}
    (D : FrameCoframeData IB V n (fun x => N (emb x)) ι) (P : (Fin d → ℝ) → B) : Prop where
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, Fin d → ℝ) n emb
  emb_mem : ∀ x, emb x ∈ S
  emb_injective : Injective emb
  contMDiffOn_P : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) IB n P T.U
  emb_P : ∀ y ∈ T.U, emb (P y) = T.proj y
  contDiffAt_ncoord : ∀ y ∈ T.U, ContDiffAt ℝ n T.ncoord y
noncomputable def tubeMap (p : TotalSpace V D.toAtlas.toCore.Fiber) : Fin d → ℝ := emb p.1 + D.toAtlas.realise p
def tubeDom : Set (TotalSpace V …) := {p | ‖D.toAtlas.realise p‖ < T.eps}
theorem image_tubeMap (h : LiftedFoot T emb D P) : tubeMap emb D '' tubeDom T emb D = T.U
noncomputable def tubeHomeomorph (h : LiftedFoot T emb D P) : OpenPartialHomeomorph (TotalSpace V …) (Fin d → ℝ)
  -- source := tubeDom, target := T.U; smooth at every grade n : ℕ∞ω
```
Non-claims: no existence of the lifted foot, no embedded level-set manifold, no tubular neighbourhood from labelled equations alone; no measure statement.

### 2.7 `LabelledNormalBundle.lean` — the only definition site of `LabelledDefiningEquations`
```lean
structure LabelledDefiningEquations (IB : ModelWithCorners ℝ EB HB) (B : Type*) [TopologicalSpace B]
    [ChartedSpace HB B] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)
    (ι : Type*) where
  emb : B → E
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, E) ∞ emb
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  u : ι → Fin k → E → ℝ
  contDiff_u : ∀ i l, ContDiff ℝ ∞ (u i l)
  indep : ∀ i, ∀ x ∈ baseSet i, LinearIndependent ℝ fun l => fderiv ℝ (u i l) (emb x)
  unit : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∀ l,
    ∃ a : ℝ, a ≠ 0 ∧ fderiv ℝ (u j l) (emb x) = a • fderiv ℝ (u i l) (emb x)
```
Derived: `diff i l x = fderiv ℝ (u i l) (emb x)`, `grad`, `tangent x = tangentOf (diff (indexAt x) · x)`, `normal x = (tangent x)ᗮ`,
`frame i x`, `frameCoframeData`, `normalAtlas`; theorems `range_frame : range (frame i x) = normal x`,
`contMDiffVectorBundle`, `coordChange_diagonal : ∃ a, (∀ l, a l ≠ 0) ∧ coordChange i j x c = toLp 2 (fun l => (a l)⁻¹ * c l)`.
Non-claims: base manifold + embedding are inputs; normal bundle realised as `(TX)ᗮ`; no quotient bundle.

### 2.8 `CoordStratumAtlas.lean`
The coordinate plane `coordPlaneModel m k = {x ∈ ℝ^{m+k} | stratumProj m k x = 0}` as a one-chart `CompatibleAnalyticLCIAtlas`,
`coordStratumAtlas_normal x = normalSpaceOf (stratumJ m k)`, and `coordStratumTube (ε) (hε) : Nonempty (AnalyticNormalTubularChart …)`.

### 2.9 `ChartStratumPieces.lean`
`sizePiece D ε I = {y | ∀ j ∈ D, (|y j| < ε ↔ j ∈ I)}` (measurable, disjoint, cover), `stratumSplit I hne : Fin d ≃ Fin (d − |I|) ⊕ Fin (|I|−1+1)`,
`integral_eq_sum_sizePiece`, `integral_sizePiece_eq_integral_condContraction` (fibre power series with radii + a.e. fibre in the ball + dominated
moments ⇒ the piece integral equals the integral of the conditional contraction series over the piece), `integral_eq_sum_pieces_nonempty_add`.
The `I = ∅` term is not estimated.

### 2.10 The core interface (verbatim)
```lean
structure CorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ) where
  ν : Measure K
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  h : Fin (n + 1) → ℕ
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  b : ℝ
  b_pos : 0 < b
  Φ : K × (Fin (n + 1) → ℝ) → U
  measurable_Φ : Measurable Φ
  c : K × (Fin (n + 1) → ℝ) → ℝ
  measurable_c : Measurable c
  nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p
  x : TangentialData K (n + 1)        -- C(K, DataSpace (n+1))
  transport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity h c p).toNNReal : ENNReal)).map Φ = target
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b,
    CoeffFamily.evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)
  fluct_zero : ∀ v, xiCoord (x v) = 0
-- chartMeasure ν n b = ν.prod (volume.restrict (piBox (n+1) (Ioc 0 b))); chartDensity h c p = (∏ p.2 i ^ h i) * c p

structure AnalyticCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)]
    (n : Fin M → ℕ) (β : ℝ) where
  core : Fin M → Measure U
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  chart : ∀ I, CorePresentation D (core I) (K I) (n I) β
```
`ResolvedNormalData.Φ` carries only `Φ_zero` and `ContinuousAt (Φ I s) 0`: no smoothness, no Jacobian, no measure compatibility;
`ResolvedCertificate.frame`/`Φ_eq` (linear frames identifying box coordinates with `N_s`) is the current substitute.

### 2.11 Mathlib (`MeasureTheory/Function/Jacobian.lean`)
```lean
theorem map_withDensity_abs_det_fderiv_eq_addHaar (hs : NullMeasurableSet s μ)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    Measure.map f ((μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) = μ.restrict (f '' s)
theorem integral_image_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ
theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (hf' …) (h'f' : ∀ x ∈ s, (f' x).det = 0) : μ (f '' s) = 0
```
(`E` finite-dimensional, `μ` an additive Haar measure on `E`; `f : E → E`.)

Reuse notes: the variable-unit strand (kernel → certificate → package/cover) is complete for the LEADING term only and is built on
`ResolutionCover`/a.e.-disjoint source images, not on `CorePresentation`; the tubular strand has two unconnected entry points
(`TubularJacobian`: concrete ℝ^d, LCI atlas, ambient change of variables with positive analytic `tubeJac`; `TubularBridge`: abstract
manifold base, conditional on `LiftedFoot`, homeomorphism only).

## 3. Questions

**Q1 (audit).** Are CCCXVIII/CCCXIX honest and correctly scoped? In particular: (a) the clamp trick — is
defining the prior/observable on all of ℝ^{n+1} via `clamp` (and `max · 0` for the prior) acceptable as
"the" prior/observable for the region `[0,b]^{n+1}`, given that the theorem's conclusion only involves their
values on the region and their normal jets at 0? (b) Is the null-tail core decomposition legitimate as a
"core + phase-gap tail" (the tail is the zero measure, so the gap `∀ᵐ z ∂0, δ₀ ≤ phase z` is vacuous)? (c)
Does the ℓ¹-continuity statement of CCCXIX actually meet your gate 2, or did you intend continuity of a
datum built from analytic data with a *derived* majorant (Cauchy estimates) rather than an assumed one?
(d) Anything in the headline rows (quoted below) that overclaims?

**Q2 (normal-unit normalisation, unit 3).** On the coordinate model with phase `K(w) = ∏_i w_i^{2k_i}` and a
compact base `B ⊂ S_I = {w : w_i = 0 ↔ i ∈ I}` (so `t(s) := ∏_{j∉I} s_j^{2k_j}` is bounded away from 0 and ∞
on `B`), give the exact construction of a `CorePresentation` at `B`: the normal map `Φ(s,v)` (presumably
`s + Σ_{i∈I} λ_i(s) v_i e_i` with `∏_i λ_i(s)^{2k_i} = t(s)^{-1}`, e.g. `λ_i(s) = t(s)^{-1/(2k_i m)}`, m=|I| —
is a symmetric split the right choice, or should the widths be chosen so the image is a fixed product set?),
the box side `b`, `β`, the density `c(s,v) = ϕ(Φ(s,v)) ∏_i λ_i(s)` (Jacobian of the normal rescaling), the
transport statement for the measure `ν_B ⊗ Leb|_{(0,b]^m}` pushed by `Φ` with this density onto
`ϕ dw|_{Φ(B × (0,b]^m)}` — which Mathlib change-of-variables lemma (`map_withDensity_abs_det_fderiv_eq_addHaar`
on ℝ^d after an `I`-coordinate split `ℝ^d ≃ ℝ^{d−m} × ℝ^m`?) and how to handle that the domain is a
`Base × (Fin m → ℝ)` product with `Base` a subtype of the stratum — and the amplitude datum: the Taylor family
of `v ↦ c(s,v) φ(Φ(s,v))` is the rescaled family `γ ↦ (fϕ⋆fφ)_γ(s) ∏λ_i(s)^{γ_i}` when ϕ, φ are given by
series in the normal variables around each `s` — which needs the series of `ϕ(s + ·)` at every base point with
a uniform radius: state the exact hypothesis you want on ϕ, φ (real-analytic on a neighbourhood of the box is
NOT enough for convergence on the box, as you noted). Is the existing variable-unit machinery (API audit in
§2) reusable here, or was it built for a different transport (source decomposition with a.e.-disjoint images)?

**Q3 (collar decomposition, unit 4).** Design the finite decomposition `μ = Σ_J μ_J + μ_tail` of the
prior-weighted Lebesgue measure on a compact box `[−a,a]^d` (or `[0,a]^d`) for the coordinate monomial
phase: which compact patches `B_J ⊂ S_I` (products of closed intervals bounded away from 0 in the
non-`I` coordinates?), which normal boxes, how to make the cores' images a.e.-disjoint and cover a
neighbourhood of the zero set `∪_i {w_i = 0} ∩ box` modulo null sets, and how to certify the uniform gap
`K ≥ δ₀` on the residual. Note the trap you flagged: after normalisation the normal widths vary with `s`,
so the images are curved boxes; how do we keep the pieces a.e.-disjoint and finitely many? Should the
collar be defined in the ORIGINAL coordinates (rectangles `|w_i| ≤ ε` for `i ∈ I`, `|w_j| ≥ ε` for `j ∉ I`)
with the normalisation applied only inside each piece (then the normal box in `v` is `s`-dependent —
which the `CorePresentation` interface does not allow, fixed `b`)? If the interface must change (e.g. allow
`b : K → ℝ` or a piecewise-constant unit), say so explicitly.

**Q4 (compatibility layer).** Given the audited statements of `LabelledNormalBundle`, `TubularBridge`,
`LabelledDefiningEquations` (§2), write the field lists (as close to compilable Lean as you can) for
`SNCNormalCompatibility`, `MonomialPhaseCompatibility`, `ResolvedDensityCompatibility` and the chart-level
`label/k_eq/h_eq/frame_conormal`, and say which of them the coordinate model (`CoordModel.geometry/normalData`)
satisfies and how to prove it. Which theorem should CONSUME them first (so that they are not decorative)?
Candidate: the theorem "the normal jets `D^r_⊥(φ∘π)(s)` in `HasCoordFreeExpansion` are the genuine normal
derivatives of `φ∘π` along the tubular map, independent of the frame" — is that the right first consumer?

**Q5 (order and stopping).** Rank units 3, 4, 5 and the compatibility layer by value per unit of effort,
estimate sizes (lines of Lean), and name the stopping point for this phase.

Please be concrete and mathematically precise; flag every place where our current interface is wrong or
too narrow, and prefer designs that reuse the audited declarations.
