# Consult #93 — the coordinate-free expansion theorem has landed; audit and direct the remaining units

You are Astra, consulted for direction on the Lean 4 formalisation (repo `timaeus-research/grammar`,
namespace `Grammar`, Mathlib, 604 modules, no sorry, axiom-clean) of the grammar paper
(Gerraty–Murfet). Your previous consults #91 (finite-part coefficients at tied crossings; keep `∑' r`;
never feed the analytic unit into the phase slot) and #92 (state the theorem on certified resolved
geometry: `ResolvedGeometry → ResolvedNormalData → certificates`; `normalTaylorForm` already has `1/r!`
so use the raw jet; exact fibre moments are not finite power–log sums; `MomentTensor V r := Dual (JetForm V r)`;
theorem as `IsLittleO` vs `n^{−A}`) set the plan. Units 1–7 have landed (CCXCVII–CCCIII). This consult:
(1) audit the landed statement for fidelity to the user's requirement — "the ultimate final formula must
have no coordinates in it at all, only conormal derivatives and quantities referring to the stratification
of the exceptional divisor"; (2) direct the remaining work.

## What landed (Lean, verbatim excerpts)

### CCXCIX `ResolvedNormalData` (unit 3) — the target predicate
abbrev MomentTensor (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (r : ℕ) : Type _ :=
  JetForm V r →L[ℝ] ℝ

namespace MomentTensor

/-- The pairing `⟨D, M⟩ = M(D)`. -/
noncomputable def pair {r : ℕ} (M : MomentTensor V r) (D : JetForm V r) : ℝ := M D

theorem pair_add {r : ℕ} (M : MomentTensor V r) (D D' : JetForm V r) :
    M.pair (D + D') = M.pair D + M.pair D' := map_add M D D'

theorem pair_smul {r : ℕ} (M : MomentTensor V r) (c : ℝ) (D : JetForm V r) :
    M.pair (c • D) = c * M.pair D := map_smul M c D

theorem add_pair {r : ℕ} (M M' : MomentTensor V r) (D : JetForm V r) :

/-- The scale `n^{−α} (log n)^j` of a power–log index. -/
noncomputable def PowerLogIndex.scale (q : PowerLogIndex) (n : ℝ) : ℝ :=
  n ^ (-q.exponent) * Real.log n ^ q.logDegree

/-! ### Resolved normal data -/

variable {d : ℕ} {U : Type*} [TopologicalSpace U]

/-- **Resolved normal data** of a resolved geometry: normal spaces, labelled conormal
differentials and tubular germs along every stratum. -/
structure ResolvedNormalData (R : ResolvedGeometry d U) (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  /-- The normal space at a point of the stratum `S_I`. -/
  N : ∀ I : Finset R.Component, R.Stratum I → Submodule ℝ A
  finrank_N : ∀ (I : Finset R.Component) (s : R.Stratum I), Module.finrank ℝ (N I s) = I.card
  /-- The labelled conormal differentials `du_i(s)`, `i ∈ I`. -/
  du : ∀ (I : Finset R.Component) (s : R.Stratum I), I → Module.Dual ℝ (N I s)
  du_linearIndependent : ∀ (I : Finset R.Component) (s : R.Stratum I), LinearIndependent ℝ (du I s)
  /-- The tubular germs `Φ_s : N_s → U`. -/
  Φ : ∀ (I : Finset R.Component) (s : R.Stratum I), N I s → U
  Φ_zero : ∀ (I : Finset R.Component) (s : R.Stratum I), Φ I s 0 = (s : U)
  continuousAt_Φ : ∀ (I : Finset R.Component) (s : R.Stratum I), ContinuousAt (Φ I s) 0

namespace ResolvedNormalData

variable {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  (D : ResolvedNormalData R A)

/-- The conormal line `ℝ · du_i(s)` of the component `i ∈ I` at `s`. -/
noncomputable def conormalLine (I : Finset R.Component) (s : R.Stratum I) (i : I) :
    Submodule ℝ (Module.Dual ℝ (D.N I s)) :=
  Grammar.conormalLine (D.du I s) i

/-- **The conormal splitting** `⊕_{i∈I} ℝ·du_i(s) ≃ N^*_s` (fibrewise, `ConormalSplitting.lean`). -/

/-! ### Stratum coefficients and the expansion coefficient -/

variable [MeasurableSpace U]

/-- **A moment coefficient field**: for every stratum, degree and power–log index, a moment tensor
at each point of the stratum. -/
abbrev MomentCoefficientField : Type _ :=
  ∀ (I : Finset R.Component) (r : ℕ), PowerLogIndex → ∀ s : R.Stratum I, MomentTensor (D.N I s) r

/-- **The stratum coefficient** `(1/r!) ∫_{S_I} ⟨D^r_⊥(φ∘π)(s), B(s)⟩ dν_I(s)`. -/
noncomputable def stratumCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component) (r : ℕ)
    (B : ∀ s : R.Stratum I, MomentTensor (D.N I s) r) : ℝ :=
  (r.factorial : ℝ)⁻¹ * ∫ s, (B s).pair (D.normalDifferential φ I s r) ∂ν I

/-- **The expansion coefficient of a power–log index**: the sum over the strata of the stratum
integrals of the normal-order series `∑_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩`. (The series is
summed pointwise inside the stratum integral: at a tied crossing the normal order is not locally
finite, and the pointwise series is the object the fibre analysis controls; when the summands are
integrable with summable integrals this is `∑_I ∑_r stratumCoefficient`.) -/
noncomputable def expansionCoefficient (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) : ℝ :=
  ∑ I : Finset R.Component, ∫ s, ∑' r : ℕ,
    (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential φ I s r) ∂ν I

/-- ★ **The coordinate-free expansion** of the original integral `∫_W φ ϕ e^{−nK}`: for every cutoff
`A`, subtracting the terms `expansionCoefficient(q) · n^{−α}(log n)^j` over the finite spectrum
`spec A` (all indices with exponent `≤ A`) leaves `o(n^{−A})`. Only the strata, the normal
differentials, the moment-tensor coefficients, the stratum densities and `π` occur. -/
def HasCoordFreeExpansion (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (B : D.MomentCoefficientField) (spec : ℝ → Finset PowerLogIndex) (W : Set (Fin d → ℝ))
    (K ϕ φ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ A : ℝ, (fun n : ℝ => globalLaplace W K (fun w => φ w * ϕ w) n -
      ∑ q ∈ spec A, D.expansionCoefficient ν B φ q * q.scale n) =o[atTop]
    fun n : ℝ => n ^ (-A)

/-- The stratum coefficient at degree `0` is an ordinary stratum integral of the observable: the
leading-measure shape. -/
theorem stratumCoefficient_zero (ν : ∀ I : Finset R.Component, Measure (R.Stratum I))
    (φ : (Fin d → ℝ) → ℝ) (I : Finset R.Component)
    (B : ∀ s : R.Stratum I, MomentTensor (D.N I s) 0) :
    D.stratumCoefficient ν φ I 0 B = ∫ s, φ (R.π s) *

### CCC `ResolvedMomentRepresentation` (unit 4): the certificate bundling the library's conditional geometric main theorem (`AdaptedStrataData`, `ChartPresentation`, `NormalMomentPresentation`) with the resolved geometry
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
  /-- The adapted strata data, with the compact stratum pieces as base spaces. -/
  adapted : AdaptedStrataData L M (fun I => ↥(base I)) n β
  /-- The normal-moment presentations (analytic fibre observables). -/
  T : ∀ I, NormalMomentPresentation (adapted.chart I)
  /-- The frames `ℝ^{n_I+1} ≃ N_s` identifying box normal coordinates with the normal space. -/
  frame : ∀ I (s : ↥(base I)), (Fin (n I + 1) → ℝ) ≃L[ℝ] D.N (strat I) s.1
  /-- The box parametrisation is the tubular germ in the frame. -/
  Φ_eq : ∀ I (s : ↥(base I)) (u : Fin (n I + 1) → ℝ),
    (adapted.chart I).Φ (s, u) = D.Φ (strat I) s.1 (frame I s u)

namespace ResolvedCertificate

variable {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}
  (C : ResolvedCertificate R D W K ϕ φ)

instance (I : Fin C.M) : CompactSpace ↥(C.base I) := isCompact_iff_compactSpace.1
  (C.isCompact_base I)
173-include hK hϕ hϕ0 hφ in
174-/-- ★★★ **The coordinate-free moment representation of the original integral**: for `N ≥ 0`,
175-`∫_W φ ϕ e^{−NK} = Σ_I ∫_{S_I} Σ'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), M̂_{I,r}(N)(s)⟩ dν_I(s) + tail(N)`.
176-Only the strata, the normal differentials, the exact moment tensors, the stratum densities and
177-`π` occur. -/
178:theorem globalLaplace_eq_tsum_stratumContraction {N : ℝ} (hN : 0 ≤ N) :
179-    globalLaplace W K (fun w => φ w * ϕ w) N =
180-      ∑ I, (∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
181-        (C.exactMoment I hN s r).pair (D.normalDifferential φ (C.strat I) s.1 r) ∂C.adapted.ν I) +
182-      C.adapted.tail N := by
183-  rw [C.globalLaplace_eq_Z hK hϕ hϕ0 hφ N, C.adapted.Z_eq_moment_series C.T C.β_pos.le hN]
184-  congr 1
199:theorem cutoffExpansion_globalLaplace :
200-    CutoffExpansion (commonQ C.adapted.k) (commonD C.n) (globalLaplace W K fun w => φ w * ϕ w)
201-      (gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x) := by
202-  have h := C.adapted.cutoffExpansion C.β_pos

Recall the library objects: `ChartPresentation D ρ K n β` has fields `ν : Measure K` (finite), `h k : Fin (n+1) → ℕ`,
`b > 0`, `Φ : K × (Fin (n+1) → ℝ) → U`, density `c`, tangential datum `x : C(K, DataSpace (n+1))` (ℓ¹ Taylor
families of phase ξ and amplitude η), `transport : (chartMeasure ν n b).withDensity (u^h c) .map Φ = (μ|_{sublevel}).ρ`,
`phase_normal : phase (Φ p) = β ∏ u_i^{2k_i}` a.e., `amplitude_eq : evalF (toEta b (x v)) u = c(v,u) · obs(Φ(v,u))` a.e.,
`fluct_zero : ξ-part of x v = 0`. `NormalMomentPresentation C`: the fibre observable `obsFibre v u = obs(Φ(v,u))` has a
power series `p v` on a ball of radius `> b`, and `c ≤ cBound`. `AdaptedStrataData`: a finite sublevel partition with a
chart presentation per piece; `gCoeff ν h k β b x μ j = Σ_I ∫_{K_I} dataBoxCoeff (x v) μ j dν_I` are the assembled
canonical coefficients, `dataBoxCoeff x μ j = boxCoeff n h k β b (toXi b x) (toEta b x) μ j` the paper's Taylor-tree
coefficients on the box. `CutoffExpansion Q D Z c := ∀ L > 0, ∃ K, ∀ᶠ N, |Z N − Σ_{μ ∈ Q⁻¹ℕ, μ < L} N^{−μ} Σ_{j ≤ D} c μ j (log N)^j| ≤ K N^{−L}(1+log N)^D`.

### CCCI `ZeroFluctSpectralKernel` (unit 5)
`monoKernel_{μ,j}(γ)` = the `(μ,j)` canonical coefficient of `∫ u^{γ+h} e^{−βN u^{2k}} du` (unit box); at zero fluctuation
`spectralCoeff 0 η μ j = Σ_{(γ,c)∈η} c·monoKernel(γ)` (all phase orders `p ≥ 1` vanish); for ℓ¹ `cη`,
`familySpectralCoeff 0 cη μ j = Σ'_γ cη_γ monoKernel(γ)`; `boxCoeff 0 cη μ j = Σ'_γ cη_γ boxSpectralKernel_{μ,j}(γ)` for
`b`-weighted ℓ¹ `cη` (`AbsSummableAt cη b := Summable (|cη γ| b^{|γ|})`), `|boxSpectralKernel(γ)| ≤ C b^{|γ|}`;
`AbsSummableAt` closed under the Cauchy product `conv`.

### CCCII `ChartCoefficientTensors` (unit 6)
theorem summable_shiftedKernel_term (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {cc : CoeffFamily (n + 1)} (hcc : AbsSummableAt cc b) (δ : Fin (n + 1) → ℕ) :
    Summable fun γ => cc γ * boxSpectralKernel n h k β b μ j (γ + δ) := by
  refine Summable.of_norm_bounded
    (hcc.mul_right (boxSpectralKernelBound n h k β b μ j * b ^ (∑ i, δ i))) fun γ => ?_
    (T : JetForm (Fin (n + 1) → ℝ) r) :
    chartMomentCoeff n h k β b μ j cc r T = ∑ bb ∈ Finset.Nat.antidiagonalTuple (n + 1) r,
      (Nat.multinomial Finset.univ bb : ℝ) * shiftedKernel n h k β b μ j cc bb *
        weightComponent T bb := by
  unfold chartMomentCoeff
/-- `(1/r!) ⟨D^rF(0), B_{r,μ,j}⟩ = ∑_{|b|=r} (∂^bF(0)/b!) K^{cc}_{μ,j}(b)`. -/
theorem inv_factorial_mul_chartMomentCoeff_apply (cc : CoeffFamily (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ) (r : ℕ) :
    (r.factorial : ℝ)⁻¹ * chartMomentCoeff n h k β b μ j cc r (normalJet F r) =
      ∑ bb ∈ Finset.Nat.antidiagonalTuple (n + 1) r,

/-- **The termwise identity, summation form**: the normal-degree series
`∑_r (1/r!) ⟨D^rF(0), B_{r,μ,j}⟩` converges to the canonical coefficient
`boxCoeff 0 (cc ⋆ jetFamily F) μ j`. -/
theorem hasSum_inv_factorial_mul_chartMomentCoeff (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {cc : CoeffFamily (n + 1)} (hcc : AbsSummableAt cc b) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : AbsSummableAt (jetFamily n F) b) :
    HasSum (fun r => (r.factorial : ℝ)⁻¹ * chartMomentCoeff n h k β b μ j cc r (normalJet F r))
      (boxCoeff n h k β b 0 (CoeffFamily.conv cc (jetFamily n F)) μ j) := by
  set K := boxSpectralKernel n h k β b μ j with hKdef
  set jf := jetFamily n F with hjf
(`weightComponentL b` is the CLM `A ↦ ∂^b A` = average of `A(e_{m_1},…,e_{m_r})` over words `m` of weight `b`;
`Nat.multinomial univ b = r!/b!`; `normalJet F r = iteratedFDeriv ℝ r F 0`.) Proof: `boxCoeff_zero_eq_tsum`, regroup the
Cauchy product along `γ = α + δ`, Fubini for the absolutely summable pair family, degree fibration.

### CCCIII `ResolvedCoordFreeExpansion` (unit 7) — THE THEOREM

/-- **A coefficient certificate**: along every chart, a `b`-weighted ℓ¹ Taylor family of the
density factor, the `b`-weighted ℓ¹ summability of the observable's Taylor family, and the
identification of the chart's amplitude datum with their Cauchy product. -/
structure CoefficientCertificate where
  /-- The Taylor family of the density factor `c(s, ·)` at the base point `s`. -/
  cc : ∀ J, ↥(C.base J) → CoeffFamily (C.n J + 1)
  cc_abs : ∀ J s, AbsSummableAt (cc J s) (C.adapted.b J)
  /-- The observable's Taylor family on the box is `b`-weighted ℓ¹. -/
  jet_abs : ∀ J s,
    AbsSummableAt (jetFamily (C.n J) ((C.adapted.chart J).obsFibre s)) (C.adapted.b J)
  /-- The amplitude datum is the Cauchy product of the density family and the observable's
  Taylor family. -/
  datum_eq : ∀ J s, toEta (C.adapted.b J) ((C.adapted.chart J).x s) =
88:noncomputable def pushedMeasure (J : Fin C.M) : Measure (R.Stratum (C.strat J)) :=
89-  (C.adapted.ν J).map Subtype.val
90-
157-/-- **The stratum density** `ν_I`: the sum over the charts presenting `S_I` of the pushforwards
158-of their base measures. -/
159:noncomputable def stratumMeasure (I : Finset R.Component) : Measure (R.Stratum I) :=
160-  ∑ J, if hJ : C.strat J = I then C.transportMeasure hJ (C.pushedMeasure J) else 0
161-
187-/-- The Radon–Nikodym weight `dν_J/dν_I` of a chart in its stratum density. -/
188:noncomputable def weight {J : Fin C.M} {I : Finset R.Component} (hJ : C.strat J = I)
189-    (s : R.Stratum I) : ℝ :=
190-  ((C.transportMeasure hJ (C.pushedMeasure J)).rnDeriv (C.stratumMeasure I) s).toReal
191-
198-/-- The chart coefficient tensor at a base point, transported to the normal space along the
199-frame. -/
200:noncomputable def chartTensor (J : Fin C.M) (s : ↥(C.base J)) (r : ℕ) (q : PowerLogIndex) :
201-    MomentTensor (D.N (C.strat J) s.1) r :=
202-  (chartMomentCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J) q.exponent
203-    q.logDegree (Cc.cc J s) r).pushFrame
204-    (C.frame J s : (Fin (C.n J + 1) → ℝ) →L[ℝ] D.N (C.strat J) s.1)
205-
206-omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
228-omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
229-/-- **The per-point identity**: the canonical coefficient of the chart datum at `s` is the
230-normal-order series of the pairings of the normal differentials with the coefficient tensors. -/
231:theorem hasSum_chartTensor_pair (J : Fin C.M) (s : ↥(C.base J)) (q : PowerLogIndex) :
232-    HasSum (fun r : ℕ => (r.factorial : ℝ)⁻¹ *
233-        (Cc.chartTensor J s r q).pair (D.normalDifferential φ (C.strat J) s.1 r))
234-      (dataBoxCoeff (C.n J) (C.adapted.h J) (C.adapted.k J) C.β (C.adapted.b J)
235-        ((C.adapted.chart J).x s) q.exponent q.logDegree) := by
236-  unfold dataBoxCoeff
237-  rw [toXi_eq_zero ((C.adapted.chart J).fluct_zero s), Cc.datum_eq J s]
253-/-- The chart coefficient tensor extended by zero off the compact base. -/
254:noncomputable def chartTensorExt (J : Fin C.M) (s : R.Stratum (C.strat J)) (r : ℕ)
255-    (q : PowerLogIndex) : MomentTensor (D.N (C.strat J) s) r :=
256-  if hs : s ∈ C.base J then Cc.chartTensor J ⟨s, hs⟩ r q else 0
257-
313-/-- **The moment coefficient field** `B_{I,r,q}(s) = ∑_J (dν_J/dν_I)(s) · B_{J,r,q}(s)`. -/
314:noncomputable def field : D.MomentCoefficientField := fun I r q s =>
315-  ∑ J, if hJ : C.strat J = I then
316-    C.weight hJ s • C.transportTensor hJ r (fun s' => Cc.chartTensorExt J s' r q) s else 0
317-
318-omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
374-/-- ★★ **The coordinate-free expansion coefficients are the assembled canonical coefficients.** -/
375:theorem expansionCoefficient_eq_gCoeff (q : PowerLogIndex) :
376-    D.expansionCoefficient C.stratumMeasure Cc.field φ q =
377-      gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x q.exponent
378-        q.logDegree := by
379-  unfold ResolvedNormalData.expansionCoefficient gCoeff
420-
421-/-- **The spectrum below the cutoff**: the lattice points `α ∈ Q⁻¹ℕ`, `α < max(A+1,1)`, with all
422-log degrees `j ≤ D`. -/
423:noncomputable def spectrumBelow (Q Dg : ℕ) (A : ℝ) : Finset PowerLogIndex :=
424-  (latticeBelow Q (cutoffExponent A) ×ˢ Finset.range (Dg + 1)).map PowerLogIndex.ofPair
425-
426-theorem sum_spectrumBelow (Q Dg : ℕ) (A : ℝ) (c : ℝ → ℕ → ℝ) (N : ℝ) :
482-
483-omit [MeasurableSpace A] [BorelSpace A] in
484-/-- ★★★ **THE COORDINATE-FREE EXPANSION** of the original integral `∫_W φ ϕ e^{−nK}`: for every
485-cutoff `A`, with the stratum densities `ν_I` and the moment coefficient fields `B_{I,r,α,j}`
486-determined by the certificates,
487-`∫_W φ ϕ e^{−nK} − ∑_{(α,j), α < max(A+1,1), j ≤ D} n^{−α}(log n)^j
488-  ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,α,j}(s)⟩ dν_I(s) = o(n^{−A})`.
489-No coordinates occur in the statement: only the strata of the exceptional divisor, the normal
490-differentials, the coefficient tensor fields, the stratum densities and `π`. -/
491:theorem hasCoordFreeExpansion (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
492-    (hφ : Measurable φ) :
493-    D.HasCoordFreeExpansion C.stratumMeasure Cc.field
494-      (spectrumBelow (commonQ C.adapted.k) (commonD C.n)) W K ϕ φ := by
495-  intro Ac

All of CCC–CCCIII: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Questions

1. **Fidelity audit.** Does `hasCoordFreeExpansion` meet the requirement? The statement mentions `R.Stratum I`,
   `D.normalDifferential φ I s r` (the raw normal jet of `φ∘π∘Φ_s` at `0`), the tensor fields `Cc.field I r q s`, the
   measures `C.stratumMeasure I`, `π`, and the spectrum `spectrumBelow Q D A ⊆ Q⁻¹ℕ × {0..D}`. Hidden coordinate
   dependence to assess: (a) `field` is built from the chart tensors pushed along the frames `e_s` and weighted by
   Radon–Nikodym derivatives `dν_J/dν_I` — is the RESULTING field intrinsic (chart-independent) given `(ν_I, Φ)`? I
   believe: the pairing `⟨D^r_⊥(φ∘π)(s), B_{J,r,q}(s)⟩` is frame-independent (frame covariance, `chartTensor_pair`), but
   `B_{J,r,q}` itself depends on the chart's density `c` and box side `b` — the paper's `B_{I,r,α,j}` also depends on the
   chosen tubular data and the partition, and only the total is canonical. Is it acceptable that we assert existence of
   `(ν_I, B_{I,r,q})` rather than their canonicity, or should the statement be reorganised so that the total functional
   `φ ↦ Σ_I ∫ Σ'_r …` is shown unique (by `CutoffExpansion` uniqueness) — and does the library need a uniqueness theorem
   for cutoff expansions? (b) The spectrum `Q⁻¹ℕ` with `Q = ∏_I Q_I` and `D = max n_I` comes from the charts; is it fine
   to quantify over a finite spectrum given by the certificate (the theorem allows any `spec`)? (c) `expansionCoefficient`
   sums the normal-order series pointwise INSIDE the stratum integral (`∫ Σ'_r`), not `Σ'_r ∫`: at tied crossings the
   normal order is not locally finite and no measurability/continuity of the tensor fields is assumed. Acceptable, or
   should we add the `Σ_r ∫` form under a continuity certificate?
2. **The certificates.** `ResolvedCertificate` carries `AdaptedStrataData` (the library's conditional geometric main
   theorem data) plus the frame identifications; `CoefficientCertificate` asks for the density Taylor family `cc` and
   `toEta b (x s) = cc ⋆ jetFamily(obsFibre s)`. Is `datum_eq` the right hypothesis, or should it be DERIVED from
   `amplitude_eq` (equal analytic functions on the box ⇒ equal Taylor families — a multivariate identity theorem) plus
   analyticity of `c`? What is the minimal honest certificate?
3. **Next units.** Candidates: (A) a first INSTANCE of both certificates so the theorem is non-vacuous — the isolated
   zero `K = |x|²` on a cube via the blow-up (`BlowUpCube` machinery exists: `coeff_eq_pi_rpow = π^{d/2}`) or the
   one-chart product example; which is cheapest and most convincing? (B) `jetFamily ↔ monoFamily p` identification
   (jets vs power-series coefficients through the diagonal polynomial identity, needs multivariate polynomial
   coefficient uniqueness) so `jet_abs` follows from `NormalMomentPresentation`'s radius `> (n+1)·b`; (C) the leading
   corollary `n^{λ}(log n)^{−(m−1)} ∫ → ∫ φ dμ_lead` from `hasCoordFreeExpansion` and its equality with the CCXC leading
   measure; (D) a uniqueness theorem for `CutoffExpansion` coefficients (canonicity of the total functionals); (E) the
   projector blow-up model `U = {(x,P)}` as a `ResolvedGeometry` with the `ResolvedCertificate`. Rank these; say which
   are gates and which are bookkeeping; estimate sizes.
4. **Mirror paragraph.** Draft (≤ 12 lines) the Lean remark for the paper mirror `grammar_lean.tex` at
   `thm:expectation_expansion` / the coordinate-free subsection, stating precisely what is proved (conditional on the two
   certificates), what the coefficient fields are, and the non-claims.
5. Anything false, misleading, or over-claimed in the HEADLINES phrasing "THE GOAL STATEMENT: no coordinates — only the
   strata of the exceptional divisor, the normal differentials, the moment-tensor coefficient fields, the stratum
   densities and π; the charts live inside the two certificates"?

Answer in sections 1–5, tersely, with concrete Lean-level recommendations.
