# Consult #117 — the smooth-amplitude engine after U3: design of the chart-level and coordinate-free assembly (U4–U6)

You are advising a Lean 4 (Mathlib) formalisation of the grammar paper (Gerraty–Murfet): asymptotic expansion of `Z(n) = ∫_W φ ϕ e^{−nK}` with insertions. Your consults #113–#116 designed the SMOOTH-AMPLITUDE facewise engine (route G5: smooth partitions of unity, stratum-adapted or not) as the way to close the atlas-existence gap of the analytic producer. Everything you asked for in #114/#116 through U3 is now LANDED and axiom-clean (Lean statements below, verbatim). Please review the landed statements briefly and then DESIGN the remaining units concretely for Lean: what structures to define, what theorems to prove, in what order, with the smallest path to a smooth-weight version of the coordinate-free expansion theorem.

## 1. What is landed (verbatim Lean signatures; namespace `Grammar.SmoothEngine` unless noted)

Notation: `box ι b := Set.pi univ fun _ => Ioc 0 b`, `mono a w := ∏ i, w i ^ a i`, `logSum a w := ∑ i, (a i : ℝ) * log (w i)`, `powLog Λ D c t := ∑ μ ∈ Λ, ∑ j ∈ range (D+1), c μ j * t ^ (-μ) * log t ^ j`, `latticeBelow Q L := {m/Q : m < ⌈LQ⌉₊}`, `absSpectralSum Q D c L N := ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ range (D+1), c μ j * log N ^ j`, and the repo's interface
```
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop, |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)
```
(with `CutoffExpansion.coeff_unique`, `.refine` (lattice refinement), `.pad`, `.add`, `.sum`, `.sub` already in the library).

### 1.1 The generic face theorem (CCCLXXXVIII)
```
theorem face_expansion {G : (ι → ℝ) → ℝ} {Z' : ℝ → ℝ} {p h a : ι → ℕ} {b M C L N : ℝ}
    {Λ : Finset ℝ} {D : ℕ} {c : ℝ → ℕ → ℝ} (hb : 0 < b)
    (hG : AEStronglyMeasurable G (volume.restrict (box ι b)))
    (hGM : ∀ w ∈ box ι b, |G w| ≤ M * mono p w) (hZm : Measurable Z')
    (hZ2 : ∀ t : ℝ, 0 < t → |Z' t - powLog Λ D c t| ≤ C * t ^ (-L) * (1 + |log t|) ^ D)
    (hΛ : ∀ μ ∈ Λ, μ ≤ L) (hA : ∀ i, (a i : ℝ) * L < p i + h i + 1) (hN : 1 ≤ N) :
    |(∫ w in box ι b, G w * mono h w * Z' (N * mono a w)) -
      ∑ μ ∈ Λ, N ^ (-μ) * ∑ j ∈ range (D + 1), ∑ q ∈ range (j + 1),
        c μ j * (j.choose q) * log N ^ q * faceCoeffInt G h a b μ (j - q)| ≤
      C * M * (1 + log N) ^ D * N ^ (-L) * faceRemWeight p h a b L D
```
with `faceCoeffInt G h a b μ e := ∫ w in box ι b, G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e` and `faceRemWeight p h a b L D := ∫ w in box ι b, (∏ i, w i ^ ((p i + h i : ℝ) - a i * L)) * (1 + |logSum a w|) ^ D` (finite by the power–log integrability lemma).

### 1.2 The box-engine adapter (CCCXCI): the face monomial integral `faceMono k e β b t := ∫ u in box ι b, mono e u * exp (-(β * t) * mono (fun i => 2 * k i) u)` satisfies, for a nonempty finite `ι`,
```
theorem faceMono_two_regime [Nonempty ι] (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      |faceMono k e β b t - powLog (latticeBelow (2 * ∏ i, k i) L) (Fintype.card ι - 1) (faceMonoCoeff k e β b) t| ≤
      C * t ^ (-L) * (1 + |Real.log t|) ^ (Fintype.card ι - 1)
```
(`faceMonoCoeff` = the analytic box engine's `boxCoeff` of the monomial coefficient family after reindexing; vanishes off the lattice `(2∏k)⁻¹ℕ` and above degree `|ι|−1`). For the empty face `faceMono = exp(−βt)` with the trivial estimate.

### 1.3 The subset formula and face split (CCCXC): `faceOp p J l G` applies `T_i^{p_i}` (coordinate Taylor polynomial at `v_i = 0`) for `i ∈ J` and `R_i^{p_i}` (remainder) for `i ∉ J` over the enumeration `l`; `sum_faceOp : G v = ∑ J ∈ l.toFinset.powerset, faceOp p J l G v`; `tayList_eq_sum` (multi-index expansion over `idxL p l = {m : m_i < p_i on l, 0 off l}`); `faceTerm_integral`:
```
∫ v in box (Fin d) b, faceOp p J (List.finRange d) F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v) =
  ∑ m ∈ idxL p (lJ J), (∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹) *
    ∫ w in box {i // ¬ inJ J i} b, faceAmp p J F m w * mono (fun i : {i // ¬ inJ J i} => h i) w *
      ∫ u in box {i // inJ J i} b, mono (fun i : {i // inJ J i} => m i + h i) u *
        exp (-(β * (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)) * mono (fun i : {i // inJ J i} => 2 * k i) u)
```
with the flat face amplitude `faceAmp p J F m w := remList p (lK J) (pdMulti m (lJ J) F) (glue J 0 w)` = `(R_K^p ∂^m F)(0_J, w)` and `faceAmp_bound : |faceAmp p J F m w| ≤ (∏_{i∈K} 1/(p_i−1)!) * M * mono (p_K) w` under the rectangular mixed-derivative bound `∀ m ≤ p, ∀ v ∈ [0,b]^d, |pdMulti m (finRange d) F v| ≤ M`.

### 1.4 The depth theorem and the canonical coefficients (CCCXCII)
```
noncomputable def smoothCoeffAtDepth (F : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1),
    faceCoef k β b x.1 (fun i => x.2 i + h i) μ j * (j.choose q) *
      faceCoeffInt (faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) b μ (j - q)
-- faceIndex p = pairs (J, m) with J ⊆ Fin d, m ∈ idxL p (lJ J); faceW J m = ∏_{i∈J} 1/m_i!; DJ J = |J| − 1; faceCoef = faceMonoCoeff on the face (0 for J = ∅)

theorem smooth_expansion_at_depth (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ v : Fin d → ℝ, (∀ i, v i ∈ Icc 0 b) → |pdMulti m (List.finRange d) F v| ≤ M) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |(∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)) -
        absSpectralSum (Qamb k) (d - 1) (smoothCoeffAtDepth F h k p β b) L N| ≤ K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1))
-- Qamb k = 2 ∏ k_i

noncomputable def smoothIntegral (F) (h k) (β b N : ℝ) : ℝ := ∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)
def depthOf (h k : Fin d → ℕ) (L : ℕ) : Fin d → ℕ := fun i => 2 * k i * L - h i
def L₀ (h : Fin d → ℕ) : ℕ := (∑ i, h i) + 1
noncomputable def cutoffOf (h : Fin d → ℕ) (μ : ℝ) : ℕ := max (⌊μ⌋₊ + 1) (L₀ h)
noncomputable def smoothCoeff (F) (h k) (β b) (μ : ℝ) (q : ℕ) : ℝ := smoothCoeffAtDepth F h k (depthOf h k (cutoffOf h μ)) β b μ q

theorem exists_rect_bound (hF : ContDiff ℝ ∞ F) (p : Fin d → ℕ) (b : ℝ) : ∃ M, ∀ m, (∀ i, m i ≤ p i) → ∀ v, (∀ i, v i ∈ Icc 0 b) → |pdMulti m (List.finRange d) F v| ≤ M
theorem smoothCoeffAtDepth_eq … : two admissible cutoffs agree below their common cutoff (finite uniqueness)

theorem smooth_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) (smoothCoeff F h k β b)
theorem smoothCoeff_unique … (hc : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) c) (hμ : ∃ m : ℕ, μ = m / Qamb k) (hj : j ≤ d - 1) : c μ j = smoothCoeff F h k β b μ j
```
Also landed: the 1D theorem (`oneDim_smooth`, explicit constants), the `d = 2` tensor theorem (`twoDim_smooth`: corner jets × monomial box integrals + two edge face integrals + `O(N^{−L})`, explicit constant), finite-cutoff uniqueness (`finite_coeff_unique`), the power–log integrability lemma.

## 2. The existing downstream interface (analytic engine), for the adapter design

* `CorePresentation D target K n β` (a weighted box `K × (0,b]^{n+1}` with base measure `ν` on a compact `K`, exponents `h k`, chart `Φ`, density factor `c : K × box → ℝ` (prior × Jacobian unit × tangential cutoff), TANGENTIAL DATUM `x : C(K, DataSpace (n+1))` with `amplitude_eq : evalF (toEta b (x s)) v = c (s,v) * D.obs (Φ (s,v))` a.e. and `fluct_zero`, `phase_normal : D.phase (Φ (s,v)) = β * ∏ v_i^{2k_i}` a.e., `transport : (chartMeasure ν n b).withDensity (chartDensity h c) |>.map Φ = target`).
* `AnalyticCoreDecomposition D M K n β`: `D.μ = ∑_I core_I + tail`, `gap : δ₀ ≤ D.phase` a.e. on the tail, `chart I : CorePresentation D (core I) (K I) (n I) β`; its theorem `expansion (hβ) (L) (hL) : ∃ Kc, ∀ᶠ N, |D.Z N − absSpectralSum (commonQ A.k) (commonD n) (gCoeff A.ν A.h A.k β A.b A.x) L N| ≤ Kc * (N^(−L) (1+log N)^{commonD})`, where `gCoeff` integrates the box coefficients `dataBoxCoeff` of the analytic (ℓ¹) data over the base `ν`.
* `ResolvedCertificate` + `CoefficientCertificate` (Cauchy-product factorisation `toEta b (x s) = cc J s ⋆ jetFamily (obsFibre s)`, both `b`-weighted ℓ¹) → ★★★ `hasCoordFreeExpansion` (CCCIII): `∀ A, globalLaplace W K (φ ϕ) n − ∑_{q ∈ spec A} expansionCoefficient ν B φ q * q.scale n = o(n^{−A})`, where `expansionCoefficient ν B φ q = ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩ dν_I` — an INFINITE transverse-jet functional of the observable paired with a "moment coefficient field" `B` (this is the analytic jet functional; finite order is impossible at codim ≥ 2, cf. J4).
* The weighted producer (CCCLXXXIV, from a `WeightedDomainAtlas`: charts `φ_i` on boxes `[−a,a]^d` with exact weighted change of variables `∑_i (ω_i · |jac_i| · vol|box_i).map φ_i = vol|_W` a.e.-compatible): `SheetInputs d` requires holomorphic packets `P i : HolomorphicSignedBoxExtension a (|jacUnit_i| · prior∘φ_i) (obs∘φ_i)` (analytic prior factor and observable) and the STRATUM-ADAPTED weight hypotheses `ω_indep : ∀ i j, 0 < k i j → ∀ y, |y j| ≤ t₀ → ω i (update y j 0) = ω i y` and `ω_contOn` (continuity near the divisor); conclusion `hasCoordFreeExpansion_of_weightedDomainAtlas : ∃ C Cc, HasCoordFreeExpansion C.stratumMeasure Cc.field (spectrumLe (commonQ) (commonD)) W K prior obs`. The motivation for the smooth engine was to DROP `ω_indep`/`ω_contOn` (arbitrary smooth partitions of unity subordinate to the chart cover) and to allow smooth (non-analytic) amplitudes.

## 3. Questions — please answer concretely, in Lean-ready terms

Q1 (U4/U5 structure). Define the smooth analogue of `CorePresentation`: base measure `ν` on compact `K`, chart `Φ : K × (Fin d → ℝ) → U`, exponents `h k`, side `b`, exact monomial phase `β ∏ v^{2k}` (after unit removal, as in the analytic engine — or should the phase unit `u(s,v)` be kept and absorbed? note the analytic engine removed units by a normalising change of variables `MonomialUnitRemoval`/`StripNormalisation`), and a SMOOTH density `c : K × (Fin d → ℝ) → ℝ` (weight × prior∘Φ × |Jacobian| × observable∘Φ) that is `C^∞` in `v` for each `s` with all `v`-derivatives jointly continuous on `K × [0,b]^d`. Then the chart contribution `Z_I(N) = ∫_K smoothIntegral (c(s,·)) h k β b N dν(s)`. The pointwise theorem gives `CutoffExpansion` for each `s` with coefficients `smoothCoeff (c(s,·)) μ q`; to integrate over `s` we need (i) measurability/continuity of `s ↦ smoothCoeff (c(s,·)) μ q` (a finite sum of face coefficient integrals of `R_K^p ∂^m c(s,·)` — continuous in `s` by dominated convergence under joint continuity of the derivatives), and (ii) a UNIFORM constant `K` in `s` (the two-regime constants do not depend on `s`; the rectangular bound `M` is uniform by compactness of `K × [0,b]^d`; `faceRemWeight` does not depend on `s`) — so `|Z_I(N) − absSpectralSum Q (d−1) (∫_K smoothCoeff (c(s,·)) dν) L N| ≤ K ν(K) N^{−L}(1+log N)^{d−1}`. Is the plan to prove a UNIFORM-in-parameter version of `smooth_expansion_at_depth` (same proof, `M` uniform) the right route, and what exactly should the structure `SmoothCorePresentation` carry so that the base integration is a one-liner? Do we need `x : TangentialData` at all in the smooth setting (no — the amplitude is just `c`; please confirm the amplitude_eq/fluct_zero fields should simply disappear)?

Q2 (the phase unit). In the weighted-atlas setting `K ∘ φ_i = phaseUnit_i(w) · ∏ w^{2k}` with `phaseUnit_i` an analytic unit depending only on the non-active (tangential) coordinates, bounded below by `c_i > 0` on the box. The analytic producer removed the unit via the collar normalisation (`ChartCollar`, water level `δ/u`). For the smooth engine the cleanest option seems: absorb the unit into `β(s)`, i.e. `N β(s) ∏ v^{2k}` with `β(s) = u(s)` continuous and bounded below on `K` — the coefficients `faceMonoCoeff k e β b` and `smoothCoeff` depend on `β` explicitly (as `β^{−μ}` factors), so a base-dependent `β(s)` is fine pointwise; uniform constants need `β(s) ≥ β₀ > 0`. Is a `β : K → ℝ` field (continuous, `≥ β₀`) the right generalisation, and should I first prove `faceMono_two_regime` uniformly in `β ∈ [β₀, β₁]` (the two-regime constant depends on `β` through the box engine's `cutoffBound`)? Or is it better to reparametrise `v ↦ u(s)^{1/(2|k|)}`-type scalings? Please recommend.

Q3 (U6 — the coordinate-free statement and the coefficient functional). With smooth amplitude the canonical coefficient at `(μ, q)` is a finite sum over faces `J` and multi-indices `m` of face integrals `∫_{(0,b]^K} (R_K^p ∂^m F)(0_J, w) w^{h_K} (w^{2k_K})^{−μ} S_K(w)^{e} dw` — the observable enters through `F` and its TRANSVERSE TAYLOR REMAINDERS `R_K^p`, not only through jets on the divisor. Three options for the coordinate-free formulation: (a) state the smooth version of `hasCoordFreeExpansion` with `expansionCoefficient` replaced by a NEW canonical functional `smoothExpansionCoefficient` (defined chart-by-chart via `smoothCoeff`, canonical by `smoothCoeff_unique`/`CutoffExpansion.coeff_unique`, hence chart-independent as a scalar — the "scalar coefficient functionals are intrinsic" conclusion of CCCVIII); (b) prove that for ANALYTIC amplitudes the smooth coefficients coincide with the analytic jet functionals (by uniqueness, since both are `CutoffExpansion`s of the same integral) — giving the smooth theorem as a strict generalisation with the same coefficients where both apply; (c) express the smooth coefficient as a jet functional plus a "remainder functional". Which should be the headline, and what is the minimal statement that "saves" the main theorem of the paper (asymptotic expansion of the partition function with insertions) in the smooth-partition setting: I believe (a)+(b) — please confirm and give the exact shape of the final theorem `hasSmoothCoordFreeExpansion`.

Q4 (the weighted-atlas closure). Given a `WeightedDomainAtlas` with SMOOTH weights `ω_i` (no stratum adaptation), analytic prior/observable near the charts, analytic units: the chart amplitude `F_i(v) = ω_i(v) |jac_i(v)| prior(φ_i v) obs(φ_i v)` is `C^∞` on the box (Jacobian unit nonvanishing on the connected box, so `|jac|` smooth). The producer then needs: per chart, sign/orthant handling (the analytic producer used reflections `refl σ` to symmetric boxes `[−a,a]^d` and selected orthants); the smooth engine works on `(0,b]^d`, so per orthant we compose with the reflection — smoothness preserved. Please list the exact steps to reach `hasSmoothCoordFreeExpansion_of_weightedDomainAtlas` with NO `ω_indep`/`ω_contOn`, reusing `Sheet.*` geometry (CCCLXX–CCCLXXXIV) where possible, and say which existing pieces (collars/water levels `ChartCollar`, `pieceDatum`, `sigma` assembly, tails) survive unchanged and which must be replaced by smooth versions.

Q5 (priorities and regression tests). Order the units U4–U6 by value/risk for the next ~10 landings, each ≤ 1 module; name the regression test that certifies U6 (e.g. the cube blow-up with a smooth radial partition of unity `ρ(|x|)`, or the overlapping shifted boxes CCCLXXXVI with a smooth ramp — both currently need the stratum-adapted hypotheses). Also: is there anything in the landed statements you consider mathematically suspicious or too weak (e.g. `∃ C` constants, `Fintype.card ι − 1` degrees, the `L₀` device, coefficients defined through `cutoffOf`)?

Be concrete and Lean-ready; prefer exact statements over prose. Mathlib naming may have drifted; describe lemmas by content.
